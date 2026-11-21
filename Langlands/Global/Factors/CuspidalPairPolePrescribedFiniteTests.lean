import Langlands.Global.Factors.CuspidalPairPoleEqualNormalizedProduct

/-! # Ordinary equal-rank normalization for prescribed finite vectors -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

universe u uQ

open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelberg RankinSelbergGlobal Whittaker
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open EqualFiniteWhittakerTests FiniteWhittakerModel FiniteWhittakerDual FiniteWhittakerTensor FiniteWhittakerSemilocal
open EqualSchwartzTensor QuotientIntegration

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  (v : FinitePlace F)

local instance polePrescribedTopology : TopologicalSpace (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.topology
local instance polePrescribedValuation : ValuativeRel (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.valuativeRel
local instance polePrescribedLocalField : IsNonarchimedeanLocalField (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.localField
local instance polePrescribedMeasurable : MeasurableSpace (padicField v).Carrier := borel _
local instance polePrescribedBorel : BorelSpace (padicField v).Carrier := ⟨rfl⟩
local instance polePrescribedGLMeasurable : MeasurableSpace
    (GeneralLinear (r + 1) (padicField v).Carrier) := borel _
local instance polePrescribedGLBorel : BorelSpace (GeneralLinear (r + 1) (padicField v).Carrier) := ⟨rfl⟩
local instance polePrescribedNMeasurable : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) (padicField v).Carrier) := borel _
local instance polePrescribedNBorel : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) (padicField v).Carrier) := ⟨rfl⟩
local instance polePrescribedQMeasurable : MeasurableSpace (LeftUnipotentQuotient r (padicField v).Carrier) := borel _
local instance polePrescribedQBorel : BorelSpace (LeftUnipotentQuotient r (padicField v).Carrier) := ⟨rfl⟩
local instance polePrescribedRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance polePrescribedContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance polePrescribedSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance polePrescribedAutomorphicGroup : AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance polePrescribedLocalGroup (A : LocalRealization F (r + 1) v) : AddCommGroup A.Space := Submodule.addCommGroup _

variable (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))

/-- Record the finite Whittaker coefficient of an already prescribed tensor factor vector,
with a reference vector normalized by the same functional. -/
def factorCoefficientOfVector (ℓ : ComponentFunctionals P v ψ) (hℓ : ℓ.val ≠ 0) (a : P.localFactor v) :
    FactorCoefficient P v ψ (fun g => ℓ.val ((P.localComponent v).representation g
      ((P.presentation.localComponentEquiv P.finiteSlice.nonzero v) a))) := by
  let ℓ₀ := factorFunctional P v ψ ℓ
  have h₀ := normalizedVector ℓ₀.val (factorFunctional_ne_zero P v ψ ℓ hℓ)
  refine ⟨ℓ₀, h₀.choose, h₀.choose_spec, a, fun g => ?_⟩
  exact congrArg ℓ.val (Representation.IntertwiningMap.isIntertwining _ _
    (P.presentation.localComponentEquiv P.finiteSlice.nonzero v).toIntertwiningMap g a)

/-- For arbitrary specified factor vectors and a row test the ordinary equal-rank
finite normalization exists and is bounded on every vertical strip. -/
theorem exists_poleFiniteEqualNormalization_of_vectors (c : FinitePairLChoice P P' hP hP')
    (ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψ)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (a : P.localFactor v) (a' : P'.localFactor v) (Φ : finiteRowTest F (r + 1) v) :
    ∃ D : PoleFiniteTestVectors v ψ P P', D.leftFactor.vector = a ∧ D.rightFactor.vector = a' ∧
      ∃ N : OrdinaryIntegralNormalization (poleEqualFiniteIntegral v ψ D Φ) (c.finiteL v),
        ∀ l h : ℝ, ∃ C : ℝ, ∀ s : ℂ, l ≤ s.re → s.re ≤ h → ‖N.value s‖ ≤ C := by
  let π := (P.localComponent v).representation
  let σ := (P'.localComponent v).representation
  have hg := cuspidalUnitaryLocalGenericity F r T (cuspidalSplitCentreUnitaryCentralCharacter F r T hT)
    P v (hP v).1 (hP v).2 ψ
  have hg' := cuspidalUnitaryLocalGenericity F r T' (cuspidalSplitCentreUnitaryCentralCharacter F r T' hT')
    P' v (hP' v).1 (hP' v).2 (ψ.scale (-1))
  have hπ : IsOfWhittakerType r (standardCharacter ψ r) π := isOfWhittakerType_of_isGeneric (padicField v) hg
  have hσ : IsOfWhittakerType r (inverseStandardCharacter ψ r) σ := by
    have ht := isOfWhittakerType_of_isGeneric (padicField v) hg'
    rw [standardCharacter_scale_neg_one ψ r] at ht
    exact ht
  obtain ⟨e⟩ := hπ.2.2
  obtain ⟨e'⟩ := hσ.2.2
  let ℓ : glFunctionals ψ r π := e.symm 1
  let ℓ' : glInverseFunctionals ψ r σ := e'.symm 1
  have hℓ : ℓ.val ≠ 0 := by
    intro h
    have hz : ℓ = 0 := Subtype.ext h
    have he : (1 : ℂ) = 0 := calc
      1 = e ℓ := (e.apply_symm_apply 1).symm
      _ = e 0 := congrArg e hz
      _ = 0 := e.map_zero
    exact one_ne_zero he
  have hℓ' : ℓ'.val ≠ 0 := by
    intro h
    have hz : ℓ' = 0 := Subtype.ext h
    have he : (1 : ℂ) = 0 := calc
      1 = e' ℓ' := (e'.apply_symm_apply 1).symm
      _ = e' 0 := congrArg e' hz
      _ = 0 := e'.map_zero
    exact one_ne_zero he
  let ℓi : ComponentFunctionals P' v (inverseFinite v ψ) :=
    functionalsCongr (inverse_factorCharacter (r := r) v ψ).symm ℓ'
  have hℓi : ℓi.val ≠ 0 := hℓ'
  let f := modelMap π ℓ ((P.presentation.localComponentEquiv P.finiteSlice.nonzero v) a)
  let f' := modelMap σ ℓ' ((P'.presentation.localComponentEquiv P'.finiteSlice.nonzero v) a')
  let D : PoleFiniteTestVectors v ψ P P' :=
    ⟨f.val, f'.val, factorCoefficientOfVector v ψ ℓ hℓ a,
      factorCoefficientOfVector v (inverseFinite v ψ) ℓi hℓi a'⟩
  refine ⟨D, rfl, rfl, ?_⟩
  have hpoly := (isPadicSymmetricLPolynomial_of_le (le_refl r)).mp (c.isIntegralPolynomialAt v ψ ν hT hT')
  exact exists_padicOrdinaryEqualNormalization (padicField v) ψ ν.val hπ hσ hpoly ℓ ℓ' hℓ hℓ' f f' Φ

end Langlands.Global.CuspidalPairPoles
