import Langlands.Global.Factors.CuspidalPairPoleFiniteIntegrals
import Langlands.Global.RankinSelberg.EqualFiniteWhittakerTests
import Langlands.Global.RankinSelberg.PadicOrdinaryNormalization

/-! # Normalized finite tests on the exact factors of cuspidal presentations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open NumberField Automorphic CompletionPadic RankinSelberg RankinSelbergGlobal
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open HarmonicAnalysis MeasureTheory QuotientIntegration Whittaker
open EqualFiniteWhittakerTests FiniteWhittakerModel FiniteWhittakerSemilocal

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  (v : FinitePlace F)

local instance : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology
local instance : ValuativeRel (padicField v).Carrier := (padicField v).canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField (padicField v).Carrier := (padicField v).canonicalTopologicalData.localField
local instance : MeasurableSpace (padicField v).Carrier := borel (padicField v).Carrier
local instance : BorelSpace (padicField v).Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) (padicField v).Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) (padicField v).Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n (padicField v).Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n (padicField v).Carrier) := ⟨rfl⟩
local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance {n : ℕ} (A : LocalRealization F n v) : AddCommGroup A.Space := Submodule.addCommGroup _

local notation "abv" => normalizedAbsoluteValue (PadicField.canonicalTopologicalData (padicField v))
local notation "μ" n => unipotentQuotientHaar (PadicField.Carrier (padicField v)) n

variable (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))

/-- A pair of opposite-character finite Whittaker functions with exact realizations
on the factors of the spectral presentations. -/
structure PoleFiniteTestVectors (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') where
  left : WhittakerFunctions ψ r
  right : InverseWhittakerFunctions ψ t
  leftFactor : FactorCoefficient P v ψ left.val
  rightFactor : FactorCoefficient P' v (inverseFinite v ψ) right.val

private theorem exists_nonzero_spanning_vector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hV : Nonempty (V ≃ₗ[ℂ] ℂ)) : ∃ x : V, x ≠ 0 ∧ ∀ y : V, ∃ c : ℂ, y = c • x := by
  obtain ⟨e⟩ := hV
  have he : e (e.symm 1) = 1 := e.apply_symm_apply 1
  refine ⟨e.symm 1, fun hz => ?_, fun y => ⟨e y, e.injective ?_⟩⟩
  · rw [hz, map_zero] at he
    exact zero_ne_one he
  · rw [map_smul, he, smul_eq_mul, mul_one]

include h h' in
private theorem exists_factor_coefficients
    (hT : HasUnitaryCentralCharacter T) (hT' : HasUnitaryCentralCharacter T')
    (left : WhittakerFunctions ψ r) (hleft : left ∈ whittakerSet ψ r (P.localComponent v).representation)
    (right : InverseWhittakerFunctions ψ t)
    (hright : right ∈ inverseWhittakerSet ψ t (P'.localComponent v).representation) :
    Nonempty (FactorCoefficient P v ψ left.val) ∧
      Nonempty (FactorCoefficient P' v (inverseFinite v ψ) right.val) := by
  have hgen := cuspidalUnitaryLocalGenericity F r T hT P v (h v).1 (h v).2 ψ
  have hgen' := cuspidalUnitaryLocalGenericity F t T' hT' P' v (h' v).1 (h' v).2 (ψ.scale (-1))
  have htype := isOfWhittakerType_of_isGeneric (padicField v) hgen
  have htype' := isOfWhittakerType_of_isGeneric (padicField v) hgen'
  rw [standardCharacter_scale_neg_one ψ t] at htype'
  have hline : Nonempty (glFunctionals ψ r (P.localComponent v).representation ≃ₗ[ℂ] ℂ) :=
    htype.2.2
  have hline' : Nonempty (glInverseFunctionals ψ t (P'.localComponent v).representation ≃ₗ[ℂ] ℂ) :=
    htype'.2.2
  obtain ⟨ℓ, hℓ, hspan⟩ := exists_nonzero_spanning_vector hline
  obtain ⟨ℓ', hℓ', hspan'⟩ := exists_nonzero_spanning_vector hline'
  rw [whittakerSet_eq_coefficientModel ℓ hspan] at hleft
  rw [inverseWhittakerSet_eq_coefficientModel ℓ' hspan'] at hright
  constructor
  · exact ⟨factorCoefficient P v ψ ℓ (fun hz => hℓ (Subtype.ext hz)) ⟨left, hleft⟩⟩
  · let ℓi : ComponentFunctionals P' v (inverseFinite v ψ) :=
      functionalsCongr (inverse_factorCharacter (r := t) v ψ).symm ℓ'
    have hℓi : ℓi.val ≠ 0 := fun hz => hℓ' (Subtype.ext hz)
    let f : (coefficientModel (P'.localComponent v).representation ℓ').toSubmodule := ⟨right, hright⟩
    obtain ⟨x, hx⟩ := modelMap_surjective (P'.localComponent v).representation ℓ' f
    let fᵢ := modelMap (P'.localComponent v).representation ℓi x
    let data := factorCoefficient P' v (inverseFinite v ψ) ℓi hℓi fᵢ
    refine ⟨⟨data.functional, data.reference, data.reference_value, data.vector, fun g => ?_⟩⟩
    exact (data.coefficient_eq g).trans (congrArg
      (fun z : (coefficientModel (P'.localComponent v).representation ℓ').toSubmodule => z.val.val g) hx)

variable (c : FinitePairLChoice P P' h h')
  (ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψ)

include ν in
/-- At each spectral point, choose an equal-rank test for the prescribed finite L-factor
and realize its Whittaker functions on the two exact finite tensor factors. -/
theorem exists_poleFiniteEqualTest (hr : r = t) (hT : IsTrivialOnSplitCentre T)
    (hT' : IsTrivialOnSplitCentre T') (s₀ : ℂ) :
    ∃ D : PoleFiniteTestVectors v ψ P P', ∃ Φ : SchwartzBruhat (Fin (t + 1) → (padicField v).Carrier),
      ∃ N : OrdinaryIntegralNormalization
        (equalRankIntegral ψ abv (μ t) (hr ▸ D.left) D.right Φ) (c.finiteL v),
        N.value s₀ ≠ 0 ∧ ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖N.value s‖ ≤ C := by
  subst r
  have hP := (isPadicSymmetricLPolynomial_of_le (le_refl t)).mp (c.isIntegralPolynomialAt v ψ ν hT hT')
  have hGen := hP.normalizedGenerator_ordinaryEqual
  have hq := (padicField v).canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨R, hR⟩ := hGen.exists_laurentEval_normalizedLaurent_ne_zero
    (spectralUnit (Nat.zero_lt_one.trans hq) s₀)
  obtain ⟨left, hleft, right, hright, Φ, _, hI⟩ := R.property
  obtain ⟨⟨DL⟩, ⟨DR⟩⟩ := exists_factor_coefficients (h := h) (h' := h') v ψ
    (cuspidalSplitCentreUnitaryCentralCharacter F t T hT)
    (cuspidalSplitCentreUnitaryCentralCharacter F t T' hT') left hleft right hright
  let rValue := (⟨R, mem_zetaSpan R.property⟩ : zetaSpan _)
  exact ⟨⟨left, right, DL, DR⟩, Φ, ordinaryNormalizationOfRationalContinuation hGen hq rValue hI,
    hR, ordinaryNormalizationOfRationalContinuation_strip_bound hGen hq rValue hI⟩

/-- At each spectral point, choose an ordinary unequal-rank test for the prescribed
finite L-factor and realize its Whittaker functions on the exact factors. -/
theorem exists_poleFiniteUnequalTest {k : ℕ} (hr : r = t + (0 + k + 1))
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T') (s₀ : ℂ) :
    ∃ D : PoleFiniteTestVectors v ψ P P',
      ∃ N : OrdinaryIntegralNormalization
        (unequalRankIntegralAt 0 k hr ψ abv (μ t) (rectangularMeasure ν.val 0 (t + 1)) D.left D.right)
        (c.finiteL v),
        N.value s₀ ≠ 0 ∧ ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖N.value s‖ ≤ C := by
  subst r
  have hle : t ≤ t + (0 + k + 1) := by omega
  have hP := (isPadicSymmetricLPolynomial_of_le hle).mp (c.isIntegralPolynomialAt v ψ ν hT hT')
  have hGen := hP.normalizedGenerator_ordinaryUnequal
  have hq := (padicField v).canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨R, hR⟩ := hGen.exists_laurentEval_normalizedLaurent_ne_zero
    (spectralUnit (Nat.zero_lt_one.trans hq) s₀)
  obtain ⟨left, hleft, right, hright, _, hI⟩ := R.property
  obtain ⟨⟨DL⟩, ⟨DR⟩⟩ := exists_factor_coefficients (h := h) (h' := h') v ψ
    (cuspidalSplitCentreUnitaryCentralCharacter F (t + (0 + k + 1)) T hT)
    (cuspidalSplitCentreUnitaryCentralCharacter F t T' hT') left hleft right hright
  let rValue := (⟨R, mem_zetaSpan R.property⟩ : zetaSpan _)
  exact ⟨⟨left, right, DL, DR⟩, ordinaryNormalizationOfRationalContinuation hGen hq rValue hI,
    hR, ordinaryNormalizationOfRationalContinuation_strip_bound hGen hq rValue hI⟩

end Langlands.Global.CuspidalPairPoles
