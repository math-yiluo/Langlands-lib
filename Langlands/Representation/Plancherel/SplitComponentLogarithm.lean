import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Langlands.Representation.Plancherel.SplitTorusRealPart

/-! # The logarithm of a point of a reductive group along its split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj NNReal
open Langlands.GroupScheme

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M : GroupScheme (Spec (CommRingCat.of F))}

/-- **Logarithm vectors along a split torus.** For a split torus `A` mapping to `M` by `a`, a
vector `w` of the real cocharacter space of `A` is a logarithm vector of `m ∈ M(F)` when pairing
with `w` computes `log |ξ(m)|` for every rational character `ξ` of `M` (through its restriction
to `A`), and computes `log ‖χ(m)‖` for every character `χ` of `M(F)` trivial on the common norm
kernel (through the normalized real part of `χ ∘ a`). -/
def IsSplitComponentLogarithm (hT : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ M)
    (m : rationalPoints M) (w : RealTorusSpace.V A) : Prop :=
  (∀ ξ : rationalCharacters M,
    RealTorusSpace.pair A ((1 : ℝ) ⊗ₜ[ℤ]
        rationalCharacters.equivCharacterLattice A (characterRestrict a ξ)) w =
      Real.log (LocalField.residueNormalizedAbsoluteValue F
        (rationalCharacterEval ξ m : F))) ∧
  ∀ χ : rationalPoints M →* ℂˣ, rationalCommonNormKernel M ≤ χ.ker →
    Real.log ‖(χ m : ℂ)‖ = RealTorusSpace.pair A
      (SplitTorus.normalizedRealPart hT (χ.comp (rationalPoints.map a))) w

/-- **Existence of logarithm vectors.** Let `a : A ⟶ M` be a split component of a connected
reductive group whose character restriction is injective. Every `m ∈ M(F)` has a logarithm
vector. -/
theorem exists_splitComponentLogarithm (hM : IsConnectedReductive M) {a : A.toGrp ⟶ M}
    (hs : IsSplitComponent a) (hinj : Function.Injective (characterRestrict a))
    (m : rationalPoints M) :
    ∃ w : RealTorusSpace.V A, IsSplitComponentLogarithm hs.1.1.1 a m w := by
  have hT : IsSplitTorus A.toGrp := hs.1.1.1
  have hindex := hs.finiteIndex_range_characterRestrict hM
  set N := (characterRestrict a).range.index with hN
  have hN0 : N ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  obtain ⟨t, ht⟩ := RenardCartan.pow_index_mem_splitValuationImage a hT hinj
    ((rationalCharacterValuation M).rangeRestrict m)
  obtain ⟨c, hc⟩ := RenardCartan.exists_rationalCharacterValuation_map_eq a hT t
  set z := rationalPoints.map a (RenardCartan.uniformizerSection A (Multiplicative.ofAdd c)) with hz
  have hval : rationalCharacterValuation M z = rationalCharacterValuation M m ^ N := by
    rw [hc]
    exact congrArg Subtype.val ht
  have hker : m ^ N * z⁻¹ ∈ rationalCommonNormKernel M := by
    rw [← rationalCharacterValuation_ker]
    simp only [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hval, mul_inv_cancel]
  have hq : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hlogq : Real.log (LocalField.residueCardinality F : ℝ) ≠ 0 :=
    (Real.log_pos hq).ne'
  refine ⟨(-Real.log (LocalField.residueCardinality F : ℝ) / N) ⊗ₜ[ℤ] c, ?_, ?_⟩
  · intro ξ
    rw [RealTorusSpace.pair_tmul_tmul, one_mul,
      ← RenardCartan.rationalCharacterValuation_map_uniformizerSection a c ξ, ← hz, hval,
      toAdd_pow, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
    have hspec := rationalNormLogarithm_spec M m ξ
    rw [rationalNormLogarithm_eq_intValuation] at hspec
    rw [← hspec, Real.log_rpow (zero_lt_one.trans hq)]
    push_cast
    field_simp
  · intro χ hχ
    have hχz : χ z = χ m ^ N := by
      have h1 : χ (m ^ N * z⁻¹) = 1 := hχ hker
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h1
      exact h1.symm
    rw [SplitTorus.pair_normalizedRealPart_tmul]
    change _ = _ * normLog _ (SplitTorus.characterNorm (χ.comp (rationalPoints.map a))
      (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c)))
    rw [normLog]
    change _ = _ * (-Real.log ‖(χ z : ℂ)‖ / _)
    rw [hχz, Units.val_pow_eq_pow_val, norm_pow, Real.log_pow]
    field_simp
