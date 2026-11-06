import Langlands.Shimura.PEL.HarrisIntegralCMClosedActionLocus
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra

/-! # Reflecting rational Rosati compatibility on the existing closed action locus -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory AlgebraicGeometry Module
open Langlands.AbelianScheme Langlands.GroupScheme.Cartier
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.PolarizedFiniteLevel

universe s

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

section Reflection

variable {Φ : (E →+* ℝ) → (F →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (preservation : pullbackTensorComparisonIsIsoStatement.{s})
    (composition : PullbackTensorCompositionStatement.{s})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{s})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{s})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{s})
    (symmetry : PullbackTensorSymmetryStatement.{s})
    (stability : PicardZeroPullbackStatement.{s})
    {S : Scheme.{s}} (B : Langlands.AbelianScheme S)
    (hB : HasDualScheme B)
    (additivity : DualSchemeMapAdditivity preservation stability B B hB hB)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (geometryB : DualSchemeGeometry B hB)
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dual0" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hB hB additivity MB evaluationB MB evaluationB geometryB geometryB
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "tauO" => D.harrisHodgePELIntegralInvolution C
local notation "Compatible" => IsInvolutionCompatible preservation composition unitCoherence
  associativity comparison symmetry stability hB additivity MB evaluationB geometryB

include hu

/-- Global invertibility of positive integers reflects the finite rational Rosati equations. -/
theorem rationalRosatiBasisEquations_iff_integral
    (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB) :
    RationalRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB additivity MB evaluationB geometryB a (homToHom0 lam) ↔
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam := by
  constructor
  · intro h k
    apply Tate.ofHom_injective hu B DB
    have hk := h k
    change comp0 B B DB (homToHom0 (a (basisO k))) (homToHom0 lam) =
      comp0 B DB DB (homToHom0 lam)
        (dual0 (homToHom0 (a (tauO (basisO k))))) at hk
    rw [dualHom0_homToHom0, comp0_homToHom0, comp0_homToHom0] at hk
    exact hk
  · exact IntegralRosatiBasisEquations.rationalize D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB additivity MB evaluationB geometryB a lam

/-- Rational compatibility for the actual extension is exactly finite integral compatibility. -/
theorem rationalAction_involutionCompatible_iff_integralBasis
    (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB) :
    letI := auxiliaryStarRing D C
    Compatible (D.harrisHodgePELRationalAction C B a).toRingHom (homToHom0 lam) ↔
      IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
        comparison symmetry stability B hB MB evaluationB geometryB a lam := by
  let _ := auxiliaryStarRing D C
  exact (rationalAction_involutionCompatible_iff D C preservation composition unitCoherence
    associativity comparison symmetry stability B hB additivity MB evaluationB geometryB
    a (homToHom0 lam)).trans
      (rationalRosatiBasisEquations_iff_integral D C preservation composition unitCoherence
        associativity comparison symmetry stability B hB additivity MB evaluationB geometryB
        hu a lam)

/-- Rational compatibility for the actual extension is exactly every actual order equation. -/
theorem rationalAction_involutionCompatible_iff_integral
    (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB) :
    letI := auxiliaryStarRing D C
    Compatible (D.harrisHodgePELRationalAction C B a).toRingHom (homToHom0 lam) ↔
      IntegralRosatiEquations D C preservation composition unitCoherence associativity
        comparison symmetry stability B hB MB evaluationB geometryB a lam := by
  let _ := auxiliaryStarRing D C
  exact (rationalAction_involutionCompatible_iff_integralBasis D C preservation composition
    unitCoherence associativity comparison symmetry stability B hB additivity MB evaluationB
    geometryB hu a lam).trans
      (integralRosatiEquations_iff_basis D C preservation composition unitCoherence
        associativity comparison symmetry stability B hB additivity MB evaluationB geometryB
        a lam).symm

end Reflection

section CM

variable [IsScalarTower ℚ F A]
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (P : Prerequisites.{0})
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P)

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C

section Test

variable (T : Over S) [QuasiSeparatedSpace T.left]

local notation "BT" => Functor.obj (baseChange T.hom) B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "addT" => relativeDualSchemeMapAdditivity P.preservation P.stability T.left
  BT BT (WT).hasDual (WT).hasDual
local notation "CompatibleT" => IsInvolutionCompatible P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WT).hasDual addT (WT).inverseBundle (WT).evaluation (WT).geometry

omit [IsScalarTower ℚ F A] in
include p in
/-- On every quasi-separated test over the actual reflex field, rational and integral
Rosati compatibility agree on the same direct pullback family. -/
theorem harrisIntegralActionFullRosatiCondition_iff_involutionCompatible
    (a : O →+* CategoryTheory.End BT) :
    letI := auxiliaryStarRing D C
    harrisIntegralActionFullRosatiCondition D C P B W lam T a ↔
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) := by
  let _ := auxiliaryStarRing D C
  exact (rationalAction_involutionCompatible_iff_integral D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability BT (WT).hasDual
    addT (WT).inverseBundle (WT).evaluation (WT).geometry
    (HarrisTaylorCMWeilLevel.cmBaseTorsionUnit (T.hom ≫ p)) a lamT).symm

/-- The existing full action condition is exactly rational involution compatibility
and the unchanged normalized determinant; invertibility is derived from the structure map. -/
theorem harrisIntegralCMFullActionCondition_iff_involutionCompatible
    (a : O →+* CategoryTheory.End BT) :
    letI := auxiliaryStarRing D C
    harrisIntegralCMFullActionCondition D C P p B W lam T a ↔
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a) := by
  let _ := auxiliaryStarRing D C
  exact and_congr
    (harrisIntegralActionFullRosatiCondition_iff_involutionCompatible D C P p B W lam T a)
    Iff.rfl

/-- Every nonzero rational scalar of the fixed map detects precisely the same
full integral action condition and normalized determinant. -/
theorem harrisIntegralCMFullActionCondition_iff_rationalUnitMultiple
    (a : O →+* CategoryTheory.End BT) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    harrisIntegralCMFullActionCondition D C P p B W lam T a ↔
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom
        (rationalUnitMultiple q (homToHom0 lamT)) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a) := by
  let _ := auxiliaryStarRing D C
  exact (harrisIntegralCMFullActionCondition_iff_involutionCompatible D C P p B W lam T a).trans
    (and_congr
      (isInvolutionCompatible_rationalUnitMultiple_iff P.preservation P.composition
        P.unitCoherence P.associativity P.comparison P.symmetry P.stability
        (WT).hasDual addT (WT).inverseBundle (WT).evaluation (WT).geometry
        (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) q).symm
      Iff.rfl)

end Test

section ClosedLocus

variable [IsLocallyNoetherian S] (R : Over S)
    [LocallyOfFiniteType R.hom] [IsSeparated R.hom]
    (eR : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{0} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj R)

local notation "raw" => (relativeIntegralActionLocusTest R B basisO eR).obj
local notation "aU" => relativeIntegralActionUniversal B basisO R eR
local notation "Z" => harrisIntegralCMClosedActionLocus D C P p B W lam R eR
local notation "ι" => harrisIntegralCMClosedActionLocusInclusion D C P p B W lam R eR

variable
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))

local instance reflectionTest_isLocallyNoetherian : IsLocallyNoetherian T.obj.left := T.property

local notation "BT" => Functor.obj (baseChange T.obj.hom) B
local notation "WT" => W.pullback P T.obj.hom
local notation "lamT" => W.pullbackMap P T.obj.hom WT lam
local notation "addT" => relativeDualSchemeMapAdditivity P.preservation P.stability T.obj.left
  BT BT (WT).hasDual (WT).hasDual
local notation "CompatibleT" => IsInvolutionCompatible P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WT).hasDual addT (WT).inverseBundle (WT).evaluation (WT).geometry
local notation "classify" => relativeIntegralActionUniversalHomEquiv B basisO R eR T

/-- A raw action morphism factors through the existing closed locus exactly when its
actual rational extension satisfies the original involution and determinant conditions. -/
theorem harrisIntegralCMClosedActionLocus_factors_iff_involutionCompatible
    (f : T.obj ⟶ raw) :
    letI := auxiliaryStarRing D C
    let a := classify f
    (∃ k : T.obj ⟶ Z, k ≫ ι = f) ↔
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a) := by
  let _ := auxiliaryStarRing D C
  exact (harrisIntegralCMClosedActionLocus_factors_iff_full D C P p B W lam R eR T f).trans
    (harrisIntegralCMFullActionCondition_iff_involutionCompatible D C P p B W lam
      T.obj (classify f))

/-- The same factorization criterion holds for every nonzero rational scalar of the
canonical pulled-back map, with the identical action and determinant. -/
theorem harrisIntegralCMClosedActionLocus_factors_iff_rationalUnitMultiple
    (f : T.obj ⟶ raw) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    let a := classify f
    (∃ k : T.obj ⟶ Z, k ≫ ι = f) ↔
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom
        (rationalUnitMultiple q (homToHom0 lamT)) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a) := by
  let _ := auxiliaryStarRing D C
  exact (harrisIntegralCMClosedActionLocus_factors_iff_full D C P p B W lam R eR T f).trans
    (harrisIntegralCMFullActionCondition_iff_rationalUnitMultiple D C P p B W lam
      T.obj (classify f) q)

/-- A supplied actual action is the literal universal restriction along a unique
morphism to the existing closed locus exactly when its rational conditions hold. -/
theorem harrisIntegralCMClosedActionLocus_existsUnique_iff_involutionCompatible
    (a : O →+* CategoryTheory.End BT) :
    letI := auxiliaryStarRing D C
    (∃! k : T.obj ⟶ Z, (relativeEndRestrict B (k ≫ ι)).comp aU = a) ↔
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a) := by
  let _ := auxiliaryStarRing D C
  let e := harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T
  have value (k : T.obj ⟶ Z) :
      (e k).val = (relativeEndRestrict B (k ≫ ι)).comp aU :=
    harrisIntegralCMClosedActionLocusFullHomEquiv_apply D C P p B W lam R eR T k
  constructor
  · rintro ⟨k, hk, _⟩
    have ha := (e k).property
    rw [value, hk] at ha
    exact (harrisIntegralCMFullActionCondition_iff_involutionCompatible D C P p B W lam
      T.obj a).mp ha
  · intro ha
    have hint := (harrisIntegralCMFullActionCondition_iff_involutionCompatible D C P p B W lam
      T.obj a).mpr ha
    let k := e.symm ⟨a, hint⟩
    have hk : (relativeEndRestrict B (k ≫ ι)).comp aU = a :=
      (value k).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨a, hint⟩))
    refine ⟨k, hk, ?_⟩
    intro l hl
    apply e.injective
    apply Subtype.ext
    exact ((value l).trans hl).trans ((value k).trans hk).symm

/-- The actual classifying morphism of an integral action satisfying exactly the
original rational involution and determinant conditions. -/
def harrisIntegralCMClosedActionLocusRationalLift
    (a : O →+* CategoryTheory.End BT)
    (ha : letI := auxiliaryStarRing D C
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a)) : T.obj ⟶ Z := by
  let _ := auxiliaryStarRing D C
  exact (harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T).symm
    ⟨a, (harrisIntegralCMFullActionCondition_iff_involutionCompatible D C P p B W lam
      T.obj a).mpr ha⟩

/-- The rationally specified classifying morphism restricts the actual universal
action to precisely the original supplied integral action. -/
theorem harrisIntegralCMClosedActionLocusRationalLift_apply
    (a : O →+* CategoryTheory.End BT)
    (ha : letI := auxiliaryStarRing D C
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a)) :
    (relativeEndRestrict B
      (harrisIntegralCMClosedActionLocusRationalLift D C P p B W lam R eR T a ha ≫ ι)).comp aU =
        a := by
  let _ := auxiliaryStarRing D C
  rw [← harrisIntegralCMClosedActionLocusFullHomEquiv_apply]
  exact congrArg Subtype.val
    ((harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T).apply_symm_apply _)

/-- Every actual classifying morphism with that literal restriction equals the lift. -/
theorem harrisIntegralCMClosedActionLocusRationalLift_eq
    (a : O →+* CategoryTheory.End BT)
    (ha : letI := auxiliaryStarRing D C
      CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) ∧
        D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p) BT
          (D.harrisHodgePELRationalAction C BT a))
    (k : T.obj ⟶ Z) (hk : (relativeEndRestrict B (k ≫ ι)).comp aU = a) :
    k = harrisIntegralCMClosedActionLocusRationalLift D C P p B W lam R eR T a ha := by
  apply (harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T).injective
  apply Subtype.ext
  rw [harrisIntegralCMClosedActionLocusFullHomEquiv_apply,
    harrisIntegralCMClosedActionLocusFullHomEquiv_apply, hk,
    harrisIntegralCMClosedActionLocusRationalLift_apply]

end ClosedLocus

end CM

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
