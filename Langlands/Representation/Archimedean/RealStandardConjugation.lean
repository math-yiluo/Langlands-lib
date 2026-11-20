import Langlands.Representation.Archimedean.RealBlockCompactAdjoint
import Langlands.Representation.Archimedean.RealGKFiniteHermitianDual
import Langlands.Representation.Archimedean.RealTemperedFormProof

/-! # Complex conjugation of real standard modules -/

noncomputable section

open scoped ComplexConjugate TensorProduct Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open RealBlockPosition GramFormula

/-- Conjugate the complex exponent, retaining the compact parity or weight. -/
def realBlockConjExponent : RealBlock → RealBlock
  | .character d => .character (RealJacquetFrobenius.charData d.parity (conj d.exponent))
  | .induced d => .induced (characterOfParams d.weight (conj d.exponent))

private theorem position_data_map_conj : ∀ (ds : List RealBlock) (i : ℕ),
    realPositionSign (ds.map realBlockConjExponent) i = realPositionSign ds i ∧
    realPositionExponent (ds.map realBlockConjExponent) i = conj (realPositionExponent ds i)
  | [], _ => by simp [realPositionSign, realPositionExponent]
  | .character _ :: _, 0 => by
      simp [realBlockConjExponent, RealJacquetFrobenius.charData, realPositionSign, realPositionExponent]
  | .character _ :: ds, i + 1 => position_data_map_conj ds i
  | .induced _ :: _, 0 => by
      simp [realBlockConjExponent, realPositionSign, realPositionExponent, map_add, map_div₀,
        map_ofNat]
  | .induced _ :: _, 1 => by
      simp [realBlockConjExponent, realPositionSign, realPositionExponent, map_sub, map_div₀,
        map_ofNat]
  | .induced _ :: ds, i + 2 => position_data_map_conj ds i

private theorem conj_ofReal_cpow (x : ℝ) (hx : 0 ≤ x) (s : ℂ) :
    conj ((x : ℂ) ^ s) = (x : ℂ) ^ conj s := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne),
    Complex.conj_ofReal]

private theorem positionCharacter_map_conj (ds : List RealBlock) (i : ℕ) (x : ℝˣ) :
    realPositionCharacter (ds.map realBlockConjExponent) i x =
      conj (realPositionCharacter ds i x) := by
  obtain ⟨hsgn, hexp⟩ := position_data_map_conj ds i
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun, hsgn, hexp]
  unfold RealJacquetFrobenius.charFun
  rw [map_mul, map_pow, Complex.conj_ofReal, conj_ofReal_cpow _ (abs_nonneg _) _]

private theorem principalSeriesCharacter_map_conj {n : ℕ} (ds : List RealBlock)
    (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter (ds.map realBlockConjExponent)) a =
      conj (principalSeriesCharacter ℝ n (realPositionCharacter ds) a) := by
  unfold principalSeriesCharacter
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [positionCharacter_map_conj, map_mul, conj_ofReal_cpow _ (pow_nonneg (norm_nonneg _) _) _]
  simp [map_sub, map_div₀, map_ofNat]

private theorem inducedBlockAt_map_conj : ∀ (ds : List RealBlock) (p : ℕ),
    realInducedBlockAt (ds.map realBlockConjExponent) p =
      (realInducedBlockAt ds p).map (fun d => characterOfParams d.weight (conj d.exponent))
  | [], _ => rfl
  | .character _ :: _, 0 => rfl
  | .character _ :: ds, p + 1 => inducedBlockAt_map_conj ds p
  | .induced _ :: _, 0 => rfl
  | .induced _ :: _, 1 => rfl
  | .induced _ :: ds, p + 2 => inducedBlockAt_map_conj ds p

private theorem conj_mem_realStandardModule {n : ℕ} {ds : List RealBlock}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ realStandardModule n ds) :
    (fun g => conj (f g)) ∈ realStandardModule n (ds.map realBlockConjExponent) := by
  obtain ⟨hps, hfourier⟩ := (mem_realStandardModule_iff n ds f).mp hf
  refine ⟨⟨RealTemperedForm.contMDiff_conj hps.1, ?_⟩, ?_⟩
  · intro a u g
    change conj (f (_ * u * g)) = _
    rw [hps.2 a u g, map_mul, principalSeriesCharacter_map_conj]
  · intro p d hd j hj g
    rw [inducedBlockAt_map_conj] at hd
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hd
    rw [RealSwapFLanding.blockFourierCoefficient_conj, hfourier p e he (-j) (by simpa using hj),
      map_zero]

/-- Pointwise conjugation maps the compact-finite standard module into the module with
conjugated exponents. -/
def realStandardConjugation (n : ℕ) (ds : List RealBlock) :
    kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ⋆[ℂ]
      kFiniteFunctions (realStandardModule n (ds.map realBlockConjExponent)) (unitaryCompact ℝ n) where
  toFun f := ⟨RealBlockCompactAdjoint.conjugate (n := n) f, conj_mem_realStandardModule f.2.1,
    FiniteVectors.IsFiniteVector.map_conjugateLinear (RealBlockCompactAdjoint.conjugate (n := n)) (fun _ _ => rfl) f.2.2⟩
  map_add' f g := Subtype.ext (map_add (RealBlockCompactAdjoint.conjugate (n := n)) f.val g.val)
  map_smul' c f := Subtype.ext (map_smulₛₗ (RealBlockCompactAdjoint.conjugate (n := n)) c f.val)

@[simp]
theorem realStandardConjugation_apply_coe (n : ℕ) (ds : List RealBlock)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    ((realStandardConjugation n ds f) : Langlands.GeneralLinear n ℝ → ℂ) = fun g => conj (f.val g) :=
  rfl

/-- Conjugation of the function model is injective. -/
theorem realStandardConjugation_injective (n : ℕ) (ds : List RealBlock) :
    Function.Injective (realStandardConjugation n ds) := by
  intro f g h
  apply Subtype.ext
  funext x
  apply (starRingEnd ℂ).injective
  exact congrArg (fun F => F.val x) h

/-- Pointwise conjugation commutes with right translation. -/
theorem realStandardConjugation_compact (n : ℕ) (ds : List RealBlock)
    (k : Matrix.unitaryGroup (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    realStandardConjugation n ds (realStandardRep n ds k f) =
      realStandardRep n (ds.map realBlockConjExponent) k (realStandardConjugation n ds f) := by
  apply Subtype.ext
  rfl

/-- Pointwise conjugation commutes with right differentiation in real directions. -/
theorem realStandardConjugation_lie (n : ℕ) (ds : List RealBlock)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    realStandardConjugation n ds (realStandardLie n ds (1 ⊗ₜ X) f) =
      realStandardLie n (ds.map realBlockConjExponent) (1 ⊗ₜ X) (realStandardConjugation n ds f) := by
  apply Subtype.ext
  simp only [realStandardConjugation_apply_coe, realStandardLie_one_tmul_apply_coe]
  funext g
  exact (RealTemperedForm.rightDerivative_conj f.2.1.1.1 X g).symm

end Langlands.Archimedean
