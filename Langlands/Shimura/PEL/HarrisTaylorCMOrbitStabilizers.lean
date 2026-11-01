import Langlands.Shimura.PEL.OrbitStabilizers
import Langlands.Shimura.PEL.HarrisTaylorCMNormalActions
import Langlands.AbelianScheme.Tate.WeilPELFrame

/-! # Stabilizers of actual Harris levels on a fixed polarized object -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  {S : Scheme.{0}}
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]

local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
local notation "orbitTower" => PolarizedWeilLevel.levelTower preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu

variable (U V : HarrisLevel D) (hVU : V.subgroup ≤ U.subgroup)
  [(V.subgroup.subgroupOf U.subgroup).Normal]

/-- Two inverse-right normal translations of a level on one fixed polarized
object agree exactly when the original subgroup elements agree modulo the fine
subgroup. No rational-isogeny quotient is taken. -/
theorem representativeOrbit_normalTranslate_eq_iff
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S))
    (g k : U.subgroup) :
    letI := auxiliaryStarRing D C
    ∀ x : (orbitTower X).obj ((indexFunctor).obj V),
      (orbitTower X).map
          ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) x =
        (orbitTower X).map
          ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU k)) x ↔
      (g : OriginalGroup) * (k : OriginalGroup)⁻¹ ∈ V.subgroup := by
  let := auxiliaryStarRing D C
  intro x
  let : IsSimpleRing A := D.simple
  let Frame := WeilAdelicFrame preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
  let : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
      (D.harrisHodgePELForm C))ᵐᵒᵖ Frame :=
    weilAdelicFrameRightAction preservation composition unitCoherence associativity
      comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
      compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
  have hfree : ∀ eta : Frame, Function.Injective
      (right eta : ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
        (D.harrisHodgePELForm C) → Frame) := by
    intro eta
    exact weilAdelicFrameRightAction_injective preservation composition unitCoherence
      associativity comparison symmetry stability X.hasDual X.geometry X.inversePoincare
      X.evaluation compatibility X.polarization h X.actionObj.action A
      (D.harrisHodgePELForm C) s
      (D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution
      (hodgeRationalPELConditions D C) eta
  have horbit := RightOrbit.translate_eq_translate_iff hfree
    ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)).element
    ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU k)).element
    ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)).respects
    ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU k)).respects x.val
  have hmem :
      ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)).element⁻¹ *
          ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU k)).element ∈
        ((indexFunctor).obj V).subgroup ↔
      (g : OriginalGroup) * (k : OriginalGroup)⁻¹ ∈ V.subgroup := by
    simpa only [hodgeLevelFunctor_map_element, CompactOpenLevel.normalInverseArrow_element,
      map_inv, inv_inv, map_mul] using
      (hodgeLevelFunctor_obj_mem D C V
        ((g : OriginalGroup) * (k : OriginalGroup)⁻¹))
  constructor
  · intro heq
    exact hmem.mp (horbit.mp (congrArg Subtype.val heq))
  · intro hmem'
    exact Subtype.ext (horbit.mpr (hmem.mpr hmem'))

/-- The stabilizer of an actual fixed-object Harris level under the original
coarse subgroup is precisely the fine subgroup. -/
theorem representativeOrbit_normalTranslate_eq_self_iff
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S))
    (g : U.subgroup) :
    letI := auxiliaryStarRing D C
    ∀ x : (orbitTower X).obj ((indexFunctor).obj V),
      (orbitTower X).map
          ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) x = x ↔
      (g : OriginalGroup) ∈ V.subgroup := by
  let := auxiliaryStarRing D C
  intro x
  have hiff := representativeOrbit_normalTranslate_eq_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s hs htor hu U V hVU X g 1 x
  rw [CompactOpenLevel.normalInverseArrow_one, (hodgeLevelFunctor D C).map_id,
    (orbitTower X).map_id] at hiff
  simpa only [Subgroup.coe_one, inv_one, mul_one, types_id_apply] using hiff

/-- The actual residual group embeds in the fixed-object fine level through
its original inverse-right transporter maps. -/
def representativeOrbitResidualEmbedding
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S)) :
    letI := auxiliaryStarRing D C
    ∀ _x : (orbitTower X).obj ((indexFunctor).obj V),
      (U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) ↪
        (orbitTower X).obj ((indexFunctor).obj V) := by
  let := auxiliaryStarRing D C
  intro x
  refine ⟨Quotient.lift
    (fun g : U.subgroup => (orbitTower X).map
      ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) x) ?_, ?_⟩
  · intro g k hrel
    apply (representativeOrbit_normalTranslate_eq_iff D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h s hs htor hu U V hVU X g k x).mpr
    have heq : (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) = k :=
      Quotient.sound hrel
    have hdiv := QuotientGroup.eq_iff_div_mem.mp heq
    exact hdiv
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro g k heq
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact (representativeOrbit_normalTranslate_eq_iff D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h s hs htor hu U V hVU X g k x).mp heq

/-- On an original subgroup element the residual embedding is the unchanged
normal inverse-right transporter on actual compatible levels. -/
@[simp] theorem representativeOrbitResidualEmbedding_mk
    (X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S))
    (g : U.subgroup) :
    letI := auxiliaryStarRing D C
    ∀ x : (orbitTower X).obj ((indexFunctor).obj V),
      representativeOrbitResidualEmbedding D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality compatibility h s hs
          htor hu U V hVU X x
          (g : U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup) =
        (orbitTower X).map
          ((indexFunctor).map (CompactOpenLevel.normalInverseArrow U V hVU g)) x := by
  intro x
  rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
