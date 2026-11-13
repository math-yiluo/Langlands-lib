import Langlands.Shimura.PEL.HarrisTaylorCMClassStabilizers

/-! # Actual frame witnesses for a fixed Harris level orbit -/

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
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
local notation "orbitTower" => PolarizedWeilLevel.levelTower preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu
local notation "transport" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "Mult" => PolarizedWeilLevel.Multiple preservation composition
  unitCoherence associativity comparison symmetry stability square universality additivity

variable
  (X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "Frame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability X.hasDual X.geometry X.inversePoincare
  X.evaluation compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" => weilAdelicFrameRightAction preservation composition
  unitCoherence associativity comparison symmetry stability X.hasDual X.geometry
  X.inversePoincare X.evaluation compatibility X.polarization h X.actionObj.action
  A (D.harrisHodgePELForm C) s
local notation "leftAction" => weilAdelicFrameMonodromyAction preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport X.hasDual X.geometry X.inversePoincare X.evaluation
  X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
local notation "commAction" => weilAdelicFrameActionsComm preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport X.hasDual X.geometry X.inversePoincare X.evaluation
  X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
local notation "frameIsogeny" => weilAdelicFrameIsogeny preservation composition
  unitCoherence associativity comparison symmetry stability X.hasDual X.hasDual
  X.geometry X.geometry X.inversePoincare X.evaluation X.inversePoincare X.evaluation
  (additivity X X) X.polarization X.polarization compatibility rationalWeilFunctoriality
  h X.actionObj.action X.actionObj.action A (D.harrisHodgePELForm C) s

/-- An actual compatible frame whose isogeny transport is a source translation
by an element of the original Harris level subgroup. -/
def OriginalLevelFrameWitness (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj) (_he : Mult X X q e), Prop := by
  let := auxiliaryStarRing D C
  intro q e he
  let : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
      (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
  exact ∃ (eta : Frame) (u : OriginalGroup), u ∈ U.subgroup ∧
    frameIsogeny q (RationalAlgebraAction.underlyingIso e)
        (RationalAlgebraAction.intertwines e.hom) he eta =
      right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
        (D.harrisHodgePELForm C)) eta (scalarEquiv u)

/-- A fixed coarse orbit supplies an actual compatible frame and an element
of the original Harris subgroup giving its postcomposition by the isogeny. -/
theorem exists_frame_original_element_of_levelIso_fixed
    (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      OriginalLevelFrameWitness D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility
        h s additivity X U q e he := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed
  let : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
      (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
  change ∃ (eta : Frame) (u : OriginalGroup), u ∈ U.subgroup ∧
    frameIsogeny q (RationalAlgebraAction.underlyingIso e)
        (RationalAlgebraAction.intertwines e.hom) he eta =
      right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
        (D.harrisHodgePELForm C)) eta (scalarEquiv u)
  let := leftAction
  let := commAction
  obtain ⟨eta, heta⟩ := Quotient.exists_rep a.val
  have hfixedVal := congrArg Subtype.val hfixed
  change RightOrbit.map ((indexFunctor).obj U).subgroup
      (frameIsogeny q (RationalAlgebraAction.underlyingIso e)
        (RationalAlgebraAction.intertwines e.hom) he)
      (by intro eta g; apply Subtype.ext; ext x; rfl) a.val = a.val at hfixedVal
  rw [← heta] at hfixedVal
  change RightOrbit.mk ((indexFunctor).obj U).subgroup
      (frameIsogeny q (RationalAlgebraAction.underlyingIso e)
        (RationalAlgebraAction.intertwines e.hom) he eta) =
    RightOrbit.mk ((indexFunctor).obj U).subgroup eta at hfixedVal
  obtain ⟨g, hg, hframe⟩ :=
    (RightOrbit.mk_eq_mk ((indexFunctor).obj U).subgroup eta
      (frameIsogeny q (RationalAlgebraAction.underlyingIso e)
        (RationalAlgebraAction.intertwines e.hom) he eta)).mp hfixedVal.symm
  refine ⟨eta, (scalarEquiv).symm g, ?_, ?_⟩
  · exact (hodgeLevelFunctor_obj_mem D C U ((scalarEquiv).symm g)).mp
      (by simpa only [ContinuousMulEquiv.apply_symm_apply] using hg)
  · simpa only [ContinuousMulEquiv.apply_symm_apply] using hframe

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
