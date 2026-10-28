import Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyStatement
import Langlands.Representation.Whittaker.TwoBlockCellCoefficientProof
import Langlands.Representation.Induction.HeterogeneousPairs
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.HarmonicAnalysis.MatrixFourierSliceProof
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Module.LinearMap.DivisionRing

/-! # Conditional proof of the JPSS two-block extension -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory RankinSelberg

universe uF uV₁ uV₂

private theorem sqrt_inv_pow_mul (d : ℝ) (hd : 0 < d) (A : ℕ) :
    Real.sqrt ((d ^ A)⁻¹) * d ^ A = Real.rpow d ((A : ℝ) / 2) := by
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hd.le, ← Real.rpow_neg hd.le, ← Real.rpow_add hd]
  congr 1
  ring

/-- The positive induction half and the rectangular Jacobian give the positive
half power in the JPSS leading-block formula. -/
theorem twoBlockHalfModulus_mul_detPow
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (a b : ℕ) (g : GeneralLinear (b + 1) F.Carrier) :
    ((T.leviHalfModulus (twoBlockShape a b)
      ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier).symm
        (1, g)) : ℂ) * (T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1)) =
      (Real.rpow (T.normalizedAbs (Matrix.det g.val)) (((a + 1 : ℕ) : ℝ) / 2) : ℂ) := by
  have hmod : T.leviModulus (twoBlockShape a b)
      ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier).symm
        (1, g)) = (T.determinantNorm (b + 1) g ^ (a + 1))⁻¹ := by
    rw [T.leviModulus_twoBlocks]
    simp only [Shahidi.twoBlockLeviEquiv_symm_first,
      Shahidi.twoBlockLeviEquiv_symm_second, map_one, one_pow, one_div]
  rw [T.leviHalfModulus_apply, hmod]
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Real.coe_sqrt, NNReal.coe_inv, NNReal.coe_pow, T.determinantNorm_coe]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal
    (sqrt_inv_pow_mul _ (T.normalizedAbs_pos (GeneralLinear.determinant g).ne_zero) (a + 1))

private theorem appendIdentity_blockSum_entry {K : Type*} [Field K]
    (n d : ℕ) (g : GeneralLinear (n + 1) K)
    (i j : Fin ((n + 1) + d)) :
    appendIdentity n d g (Fin.cast (by omega) i) (Fin.cast (by omega) j) =
      GeneralLinear.blockSum (g, (1 : GeneralLinear d K)) i j := by
  classical
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    simp [appendIdentity_entry, Fin.ext_iff, Matrix.one_apply] <;>
      split_ifs <;> first | rfl | omega

/-- The iterated leading embedding in the target is the literal block sum
used by the cell coefficient formula. -/
theorem twoBlockLeadingEmbedding_eq {K : Type*} [Field K] (a b : ℕ)
    (g : GeneralLinear (b + 1) K) :
    GeneralLinear.reindex (finCongr (by omega : b + (a + 1) + 1 = (a + 1) + (b + 1)))
        (appendIdentity b (a + 1) g) =
      Shahidi.swapRank (a + 1) (b + 1) K (GeneralLinear.blockSum (g, 1)) := by
  apply Units.ext
  ext i j
  exact appendIdentity_blockSum_entry b (a + 1) g
    (Fin.cast (by omega) i) (Fin.cast (by omega) j)

/-- A one-dimensional standard functional space supplies a functional and
vector with value one. -/
private theorem exists_functional_vector_one
    {K : Type*} [Field K] [TopologicalSpace K]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter K) (n : ℕ)
    (π : Representation ℂ (GeneralLinear (n + 1) K) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    ∃ (ℓ : glFunctionals ψ n π) (v : V), ℓ.val v = 1 := by
  obtain ⟨e⟩ := hπ.2.2
  let ℓ : glFunctionals ψ n π := e.symm 1
  have hℓ : ℓ ≠ 0 := by
    intro h
    have := congrArg e h
    exact one_ne_zero (by
      simpa only [ℓ, LinearEquiv.apply_symm_apply, map_zero] using this)
  have hval : ℓ.val ≠ 0 := fun h => hℓ (Subtype.ext h)
  obtain ⟨v, hv⟩ := (LinearMap.surjective_iff_ne_zero.mpr hval) 1
  exact ⟨ℓ, v, hv⟩

/-- The full unchanged extension target follows once row Fourier surjectivity
is available for the canonical topology in every dimension. -/
theorem twoBlockWhittakerExtension_of_rowFourierSurjectivity :
    TwoBlockExtensionAssemblyStatement.{uF, uV₁, uV₂} := by
  intro hsurj p _ F ψ a b V₁ _ _ V₂ _ _ π₁ π₂ hπ₁ hπ₂
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  dsimp only
  let π₁' : Representation ℂ (GeneralLinear (a + 1) F.Carrier) (ULift.{uV₂} V₁) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
  let π₂' : Representation ℂ (GeneralLinear (b + 1) F.Carrier) (ULift.{uV₁} V₂) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
  have hπ₁' : IsSmooth π₁' := (isSmooth_literalULift_iff π₁).mpr hπ₁.1.1
  have hπ₂' : IsSmooth π₂' := (isSmooth_literalULift_iff π₂).mpr hπ₂.1.1
  intro W₂ hW₂ Φ
  obtain ⟨ℓ₁, v₁, hℓ₁⟩ := exists_functional_vector_one ψ a π₁ hπ₁
  obtain ⟨ℓ₂, v₂, hv₂⟩ := hW₂
  let e₁ : π₁.Equiv π₁' := literalULiftEquiv π₁
  let e₂ : π₂.Equiv π₂' := literalULiftEquiv π₂
  let ℓ₁' : glFunctionals ψ a π₁' := Whittaker.functionalsCongr e₁ ℓ₁
  let ℓ₂' : glFunctionals ψ b π₂' := Whittaker.functionalsCongr e₂ ℓ₂
  let ν : AdditiveHaarMeasure F.Carrier :=
    normalizedAdditiveHaar F.Carrier (Classical.choice inferInstance)
  obtain ⟨Ψ, hΨ⟩ := padicMatrixFourierSlice p F T a b (hsurj p F (b + 1)) ψ ν Φ
  obtain ⟨W, hW, hvalues⟩ := twoBlockCellCoefficient p F a b π₁' π₂' hπ₁' hπ₂'
    ψ ℓ₁'.val ℓ₁'.property ℓ₂'.val ℓ₂'.property
    (rectangularMeasure ν (b + 1) (a + 1)) Ψ (ULift.up v₁) (ULift.up v₂)
  refine ⟨W, hW, ?_⟩
  intro g
  rw [twoBlockLeadingEmbedding_eq, hvalues g, hΨ g]
  have hfirst : ℓ₁'.val (ULift.up v₁) = 1 := hℓ₁
  have hsecond : ℓ₂'.val (π₂' g (ULift.up v₂)) = W₂.val g := by
    change ℓ₂.val (π₂ g v₂) = W₂.val g
    exact congrArg (fun H : WhittakerFunctions ψ b => H.val g) hv₂
  rw [hfirst, one_mul, hsecond]
  let m := (Shahidi.twoBlockLeviEquiv
    (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier).symm (1, g)
  calc
    ((T.leviHalfModulus (twoBlockShape a b) m : ℂ) * W₂.val g) *
        ((T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1) * Φ (lastRow g)) =
        W₂.val g * Φ (lastRow g) *
          ((T.leviHalfModulus (twoBlockShape a b) m : ℂ) *
            (T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1)) := by ring
    _ = _ := by rw [twoBlockHalfModulus_mul_detPow]

end Langlands.Whittaker
