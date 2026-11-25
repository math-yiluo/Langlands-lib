import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction
import Langlands.Automorphic.GroupSchemeQuotientL2IntegratedRepresentative
import Langlands.Automorphic.CuspidalAdmissible.Reproduction
import Langlands.Automorphic.GroupSchemeCuspidalEnvelopingAction
import Langlands.Automorphic.GroupSchemeConstantTermEnvelopingProof
import Langlands.Global.ArchimedeanConvolutionDifferentiationProof
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Differential stability of closed invariant classes of stable automorphic forms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

set_option maxHeartbeats 900000 in
private theorem OperatorRealization.enveloping_eval_of_reproducesAt
    {F : Type u} [Field F] [NumberField F] {n : ℕ}
    [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
    (ν : Measure (InfiniteAdelicGL F n)) [IsFiniteMeasureOnCompacts ν]
    (R : OperatorRealization F n) (f : R.Space) (x : AdelicGL F n)
    (κ : ArchimedeanGL.SmoothCompactKernel F n)
    (hx : R.ReproducesAt ν κ.val.val f x) (D : ArchimedeanGL.EnvelopingAlgebra F n) :
    evaluate F n (R.toContinuous (R.envelopingAction D f)) x =
      ∫ z, evaluate F n (R.toContinuous f) (x * AdelicGL.ofInfinite F n z) *
        (ArchimedeanGL.envelopingAction F n D κ.val).val z⁻¹ ∂ν := by
  let a := AdelicGL.infinite F n x
  let b := AdelicGL.finite F n x
  let s := finiteSmoothSlice F n b (R.ambient f)
  let t := ArchimedeanGL.smoothLeftTranslation F n a s
  have hxs : AdelicGL.pair F n a b = x := AdelicGL.pair_projections F n x
  have ht (z : InfiniteAdelicGL F n) :
      t.val z = evaluate F n (R.toContinuous f) (x * AdelicGL.ofInfinite F n z) := by
    change (ArchimedeanGL.smoothLeftTranslation F n a s).val z = _
    rw [ArchimedeanGL.smoothLeftTranslation_apply]
    have hpair : x * AdelicGL.ofInfinite F n z = AdelicGL.pair F n (a * z) b := by
      rw [AdelicGL.ofInfinite_eq_pair, ← hxs, AdelicGL.pair_mul, mul_one]
    rw [hpair, R.evaluate_toContinuous]
    exact finiteSmoothSlice_apply F n b (R.ambient f) (a * z)
  have htc (z : InfiniteAdelicGL F n) : ArchimedeanGL.toContinuousMap F n t z =
      evaluate F n (R.toContinuous f) (x * AdelicGL.ofInfinite F n z) := ht z
  obtain ⟨j, hj, hD⟩ := ArchimedeanGL.compactKernelConvolutionDifferentiation F n ν
    (ArchimedeanGL.toContinuousMap F n t) κ
  have hjt : j = t := by
    apply Subtype.ext
    funext z
    rw [hj, ArchimedeanGL.rawConvolution_apply, ht z, hx z]
    simp only [htc]
  calc
    _ = (ArchimedeanGL.envelopingAction F n D s).val a := by
      rw [R.evaluate_toContinuous, R.ambient_envelopingAction, ← hxs]
      exact evaluate_finiteSmoothEnvelopingAction F n D (R.ambient f) a b
    _ = (ArchimedeanGL.envelopingAction F n D t).val 1 := by
      change _ = (ArchimedeanGL.envelopingAction F n D
        (ArchimedeanGL.smoothLeftTranslation F n a s)).val 1
      rw [ArchimedeanGL.envelopingAction_leftTranslation_eval, mul_one]
    _ = _ := by
      rw [← hjt]
      simpa only [mul_one, htc] using hD D 1

namespace GroupSchemeFunctions

open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus Langlands.GroupScheme

private theorem integral_mem_closed_submodule {Y E : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (A : Submodule ℂ E) (hA : IsClosed (A : Set E))
    {f : Y → E} (hf : Integrable f ν) (hfA : ∀ y, f y ∈ A) : (∫ y, f y ∂ν) ∈ A := by
  let : IsClosed (A : Set E) := hA
  apply (Submodule.Quotient.mk_eq_zero A).mp
  change A.mkQL (∫ y, f y ∂ν) = 0
  rw [← A.mkQL.integral_comp_comm hf]
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y =>
    (Submodule.Quotient.mk_eq_zero A).mpr (hfA y))

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

section Ambient

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "n" => r + 1
local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i
local notation "Γ" => positiveRationalSubgroup F GLs T i
local notation "Q" => PositiveRationalQuotient F GLs T i
local notation "ρ" => haarQuotientL2BoundedRightAction F GLs T i hi I e hc

/-- In a closed right-invariant submodule of the quotient `L²`, the classes of stable forms
are stable under the genuine enveloping action. The forms need not be cuspidal. -/
def GeneralLinearClosedFormClassesEnvelopingStatement : Prop :=
  ∀ [CompactSpace (AdeleQuotient F)] (A : Submodule ℂ (Lp ℂ 2 μQ)),
    IsClosed (A : Set (Lp ℂ 2 μQ)) →
    (∀ a, ∀ φ ∈ A, ρ a φ ∈ A) →
    ∀ (D : ArchimedeanGL.EnvelopingAlgebra F n) (f : StableAutomorphicFunctions F n)
      (φ : Lp ℂ 2 μQ), φ ∈ A →
      IsGeneralLinearFormClass F r T i φ (stableToContinuous F n f) →
      ∃ ψ ∈ A, IsGeneralLinearFormClass F r T i ψ
        (stableToContinuous F n (stableAutomorphicEnvelopingAction F n D f))

set_option maxHeartbeats 800000 in
/-- Use a compact reproducing kernel for `f`, differentiate the kernel and take the
resulting Bochner integral in the closed submodule. -/
theorem generalLinearClosedFormClassesEnveloping :
    GeneralLinearClosedFormClassesEnvelopingStatement F r T i hi I e hc := by
  intro _ A hA hInv D f φ hφ hf
  obtain ⟨h, hPull, hRep⟩ := hf
  let R : OperatorRealization F n := ⊤
  let fR : R.Space := ⟨f, trivial⟩
  let : SecondCountableTopology (InfiniteAdelicGL F n) :=
    (GeneralLinearGroupPoints.infiniteHomeomorph F n).symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : MeasurableSpace (InfiniteAdelicGL F n) := ArchimedeanGL.borelMeasurableSpace F n
  let : BorelSpace (InfiniteAdelicGL F n) := ArchimedeanGL.borelMeasurableSpace_borelSpace F n
  let ν := ArchimedeanGL.leftHaarMeasure F n
  let : ν.IsHaarMeasure := ArchimedeanGL.leftHaarMeasure_isHaarMeasure F n
  obtain ⟨κ, hκ⟩ := R.exists_reproducingKernel ν fR
  let m := GeneralLinearGroupPoints.adelicHomeomorph F n
  let b : C(InfiniteAdelicGL F n, AdelicGroupPoints F GLs) :=
    ⟨fun z => m.symm (AdelicGL.ofInfinite F n z),
      m.symm.continuous.comp (AdelicGL.ofInfinite F n).continuous⟩
  let κ' := ArchimedeanGL.envelopingAction F n D κ.val
  let w : C(InfiniteAdelicGL F n, ℂ) :=
    ⟨fun z => κ'.val z⁻¹, (ArchimedeanGL.continuous F n κ').comp continuous_inv⟩
  have hw : HasCompactSupport w :=
    (ArchimedeanGL.envelopingCompactSupport F n D κ.val κ.property).comp_homeomorph
      (Homeomorph.inv (InfiniteAdelicGL F n))
  obtain ⟨hI, hJ⟩ := groupSchemeQuotientL2IntegratedRepresentative F GLs T i hi I e hc ν
    b w hw φ h hRep
  refine ⟨∫ z, w z • ρ (b z) φ ∂ν,
    integral_mem_closed_submodule A hA hI (fun z => A.smul_mem (w z) (hInv (b z) φ hφ)),
    weightedQuotientOrbitIntegral F GLs T i ν b w hw h, ?_, hJ⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ContinuousRationalFunctions.evaluate F n (continuousGeneralLinearEquiv F n
    (positiveQuotientContinuousPullback F GLs T i
      (weightedQuotientOrbitIntegral F GLs T i ν b w hw h))) x =
    ContinuousRationalFunctions.evaluate F n (R.toContinuous (R.envelopingAction D fR)) x
  have hEval (k : C(Q, ℂ)) (g : AdelicGL F n) :
      ContinuousRationalFunctions.evaluate F n
        (continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLs T i k)) g =
        k (LeftCosetSpace.mk Γ (m.symm g)) := by
    rw [evaluate_continuousGeneralLinearEquiv]
    rfl
  have hPoint (g : AdelicGL F n) : h (LeftCosetSpace.mk Γ (m.symm g)) =
      ContinuousRationalFunctions.evaluate F n (R.toContinuous fR) g := by
    rw [← hEval h g, hPull]
    rfl
  rw [R.enveloping_eval_of_reproducesAt ν fR x κ (hκ x) D, hEval,
    weightedQuotientOrbitIntegral_apply]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  change w z * h (LeftCosetSpace.rightTranslate Γ (b z) (LeftCosetSpace.mk Γ (m.symm x))) =
    ContinuousRationalFunctions.evaluate F n (R.toContinuous fR) (x * AdelicGL.ofInfinite F n z) * w z
  have hProd : m.symm (x * AdelicGL.ofInfinite F n z) = m.symm x * b z := map_mul m.symm _ _
  rw [LeftCosetSpace.rightTranslate_mk, ← hProd, hPoint, mul_comm (w z)]

end Ambient

/-- The attached stable cuspidal forms are differentially stable in their given closed
invariant subspace; pointwise cuspidality is preserved by the actual constant terms. -/
theorem generalLinearSummandFormsEnveloping : GeneralLinearSummandFormsEnvelopingStatement.{u} := by
  intro F _ _ _ r hPD T i hi _ I _ e hc _ hG S πc P hP hInv D f hf
  obtain ⟨hfC, φ, hφP, hfφ⟩ := (mem_summandForms F r T i _ f).mp hf
  let G := GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
  let E := Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)
  let A : Submodule ℂ E := P.map S.subtype
  have hS : IsClosed (S : Set E) :=
    (fullAEL2CuspidalClosedSubmodule F G hPD hG T i hi I e hc).isClosed
  have hA : IsClosed (A : Set E) := hS.isClosedEmbedding_subtypeVal.isClosedMap _ hP
  have hInvA (a : AdelicGroupPoints F G) (v : E) (hv : v ∈ A) :
      haarQuotientL2BoundedRightAction F G T i hi I e hc a v ∈ A := by
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨πc a p, hInv a p hp, rfl⟩
  exact (mem_summandForms F r T i A _).mpr
    ⟨generalLinearCuspidal_envelopingAction F (r + 1) adelicConstantTermEnveloping D hfC,
      generalLinearClosedFormClassesEnveloping F r T i hi I e hc A hA hInvA D f φ hφP hfφ⟩

end GroupSchemeFunctions

end Langlands.Automorphic
