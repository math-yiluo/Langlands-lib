import Langlands.Global.RankinSelberg.FiniteWhittakerSemilocalProduct
import Langlands.Global.RankinSelberg.PadicEqualNonvanishingTests
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity

/-! # Finite equal-rank Whittaker tests on actual presentation components -/

noncomputable section
open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.EqualFiniteWhittakerTests

open Langlands.Automorphic Langlands.Global.CompletionPadic
open Langlands.Global.FiniteAdelicGL
open Langlands.Global.CuspidalPairFunctionalEquation
open FiniteWhittakerTensor FiniteWhittakerModel FiniteWhittakerSemilocal

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance : AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance {v : FinitePlace F} (L : LocalRealization F (r + 1) v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

section Local

variable {T T' : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{u, uQ} T)
  (P' : CuspidalSpectralPresentation.{u, uQ} T')
  (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
  (v : FinitePlace F)

variable (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
  (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))

/-- A normalized reference vector and a vector realizing a specified coefficient on
the exact finite factor of the supplied presentation. -/
structure FactorCoefficient (f : FiniteLocalGL F (r + 1) v → ℂ) where
  functional : FactorFunctionals P v ψ
  reference : P.localFactor v
  reference_value : functional.val reference = 1
  vector : P.localFactor v
  coefficient_eq : ∀ g : FiniteLocalGL F (r + 1) v,
    functional.val ((P.localFactor v).representation g vector) = f g

/-- Pull back a nonzero functional, choose a normalized reference and realize
the prescribed function using the exact local equivalence. -/
def factorCoefficient (ℓ : ComponentFunctionals P v ψ) (hℓ : ℓ.val ≠ 0)
    (f : (Whittaker.coefficientModel (P.localComponent v).representation ℓ).toSubmodule) :
    FactorCoefficient P v ψ f.val.val := by
  let h := normalizedVector (factorFunctional P v ψ ℓ).val (factorFunctional_ne_zero P v ψ ℓ hℓ)
  let a := factorVectorData P v ψ ℓ f
  exact ⟨factorFunctional P v ψ ℓ, Classical.choose h, Classical.choose_spec h, a.val, a.property⟩

local instance : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology
local instance : TopologicalSpace (FiniteLocalGL F (r + 1) v) :=
  (padicField v).canonicalGeneralLinearTopology (r + 1)
local instance : ValuativeRel (padicField v).Carrier := (padicField v).canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.localField
local instance : MeasurableSpace (padicField v).Carrier := borel (padicField v).Carrier

/-- The local test data use the original embedded actions with the canonical topology. -/
abbrev TestData : Type u :=
  EqualLocalTestData (padicField v) ψ ν (V := (P.localComponent v).Space) (W := (P'.localComponent v).Space)
    (P.localComponent v).representation (P'.localComponent v).representation

omit [CompactSpace (AdeleQuotient F)] in
/-- The second test functional has the same character as the canonical inverse
component used by finite tensor separation. -/
theorem inverse_factorCharacter :
    factorCharacter (r := r) v (inverseFinite v ψ) =
      Whittaker.inverseStandardCharacter ψ r := by
  apply MonoidHom.ext
  intro n
  apply Units.ext
  simp only [factorCharacter, inverseFinite, Whittaker.standardCharacter_apply,
    Whittaker.inverseStandardCharacter_apply, complex_inverseCharacter, AddChar.inv_apply']

/-- View the second test functional as a functional for the canonical inverse component. -/
def inverseComponentFunctional (D : TestData P P' v ψ ν) :
    ComponentFunctionals P' v (inverseFinite v ψ) :=
  RankinSelberg.functionalsCongr (inverse_factorCharacter (r := r) v ψ).symm D.ℓ'

/-- The second test function has the same values in the coefficient model
for the canonical inverse component. -/
theorem exists_inverseModelVector (D : TestData P P' v ψ ν) :
    ∃ f : (Whittaker.coefficientModel (P'.localComponent v).representation
        (inverseComponentFunctional P P' v ψ ν D)).toSubmodule,
      ∀ g : FiniteLocalGL F (r + 1) v, f.val.val g = D.f'.val.val g := by
  obtain ⟨a, ha⟩ := Whittaker.modelMap_surjective (P'.localComponent v).representation D.ℓ' D.f'
  refine ⟨Whittaker.modelMap (P'.localComponent v).representation
    (inverseComponentFunctional P P' v ψ ν D) a, fun g => ?_⟩
  exact congrArg (fun f : (Whittaker.coefficientModel (P'.localComponent v).representation
    D.ℓ').toSubmodule => f.val.val g) ha

/-- The second test function is realized exactly on the supplied factor for the inverse
canonical component. -/
def inverseFactorCoefficient (D : TestData P P' v ψ ν) :
    FactorCoefficient P' v (inverseFinite v ψ) D.f'.val.val := by
  let h := exists_inverseModelVector P P' v ψ ν D
  let a := factorCoefficient P' v (inverseFinite v ψ)
    (inverseComponentFunctional P P' v ψ ν D) D.ℓ'_ne_zero (Classical.choose h)
  exact ⟨a.functional, a.reference, a.reference_value, a.vector,
    fun g => (a.coefficient_eq g).trans (Classical.choose_spec h g)⟩

include hP in
private theorem component_generic :
    Whittaker.IsGeneric ψ r (V := (P.localComponent v).Space)
      (P.localComponent v).representation := by
  have hχ : CuspidalWhittaker.localCharacter F v ≠ 1 := by
    intro he
    obtain ⟨t, ht⟩ := CuspidalWhittaker.exists_localCharacter_ne_one F v
    exact ht (by rw [he, AddChar.one_apply])
  obtain ⟨ℓ, hℓ, heq⟩ := CuspidalWhittaker.exists_localWhittakerFunctional (P.localComponent v)
    (P.localComponent_isCuspidal v) (P.localComponent_ne_bot v)
  exact (P.localComponent v).isGeneric_of_integerTrivial_character (hP v).1 (hP v).2
    (CuspidalWhittaker.localCharacter F v) hχ
    (fun _ hx => CuspidalWhittaker.localCharacter_eq_one F hx) ℓ hℓ heq ψ

include hP hP' in
/-- The published p-adic unit-value and functional-equation results supply both
right-half-plane nonvanishing clauses on the target's actual local representations. -/
theorem exists_tests (hν : Correspondence.IsSelfDualMeasure (padicField v) ψ ν) :
    ∃ D : TestData P P' v ψ ν,
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.integral s ≠ 0) ∧
      ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.dualIntegral s ≠ 0 := by
  have hgen := component_generic P hP v ψ
  have hgen' := component_generic P' hP' v (ψ.scale (-1))
  have hW := RankinSelberg.isOfWhittakerType_of_isGeneric (padicField v) hgen
  have hW' := RankinSelberg.isOfWhittakerType_of_isGeneric (padicField v) hgen'
  rw [RankinSelberg.standardCharacter_scale_neg_one] at hW'
  obtain ⟨ℓ, hℓ⟩ := hgen.2.2
  obtain ⟨ℓ', hℓ'⟩ := hgen'.2.2
  obtain ⟨D, _, _, _, hn, hn'⟩ := EqualNonvanishing.padicEqualNonvanishingTest (padicField v) ψ ν hν
    r (P.localComponent v).Space (P'.localComponent v).Space
    (P.localComponent v).representation (P'.localComponent v).representation
    hW hW' ℓ (RankinSelberg.functionalsCongr (RankinSelberg.standardCharacter_scale_neg_one ψ r) ℓ')
    hℓ hℓ'
  exact ⟨D, hn, hn'⟩

/-- The two finite model functions have reciprocal unipotent characters. -/
theorem pair_invariant (D : TestData P P' v ψ ν)
    (n : Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v))
    (g : FiniteLocalGL F (r + 1) v) :
    D.f.val.val (n.val * g) * D.f'.val.val (n.val * g) =
      D.f.val.val g * D.f'.val.val g := by
  let χ := Whittaker.standardCharacter ψ r n
  have h₁ : D.f.val.val (n.val * g) = (χ : ℂ) * D.f.val.val g := D.f.val.property n g
  have h₂ : D.f'.val.val (n.val * g) = (χ : ℂ)⁻¹ * D.f'.val.val g := D.f'.val.property n g
  have hcancel (a b : ℂ) : ((χ : ℂ) * a) * ((χ : ℂ)⁻¹ * b) = a * b := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ χ.ne_zero, one_mul]
  calc
    _ = ((χ : ℂ) * D.f.val.val g) * ((χ : ℂ)⁻¹ * D.f'.val.val g) :=
      congrArg₂ (fun z w : ℂ => z * w) h₁ h₂
    _ = _ := hcancel _ _

end Local

end Langlands.Global.RankinSelbergGlobal.EqualFiniteWhittakerTests
