import Langlands.Shimura.PEL.HarrisTaylorCMFiniteOrderReduction

/-! # Local coordinates of actual Harris frames -/

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

omit hμfin hμet in
/-- Coordinates of an actual rational Tate section in a chosen compatible frame,
then evaluated at the specified actual finite completion. -/
def localFrameCoordinate (v : Global.FinitePlace ℚ) :
    letI := auxiliaryStarRing D C
    Frame → RationalFull X.actionObj.abelianScheme (Over.mk s) →
      (Global.FiniteCompletion ℚ v) ⊗[ℚ] A := by
  let := auxiliaryStarRing D C
  intro eta y
  exact AlgebraInvolution.changeCoefficients (AlgebraInvolution.finiteEvaluation v)
    (eta.1.symm y)

omit hμfin hμet in
/-- The actual frame equation becomes right multiplication by the evaluated
original Harris element in local frame coordinates. -/
theorem localFrameCoordinate_frame_isogeny (v : Global.FinitePlace ℚ) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e)
      (eta : Frame) (u : OriginalGroup),
      (letI : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
       frameIsogeny q (RationalAlgebraAction.underlyingIso e)
          (RationalAlgebraAction.intertwines e.hom) he eta =
        right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C)) eta (scalarEquiv u)) →
      ∀ y : RationalFull X.actionObj.abelianScheme (Over.mk s),
        localFrameCoordinate D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h s X v eta
            (rationalHomMap (Over.mk s) (fun _ => True)
              (RationalAlgebraAction.hom0 e.hom) y) =
          localFrameCoordinate D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality compatibility h s X v eta y *
            AlgebraInvolution.changeCoefficients (AlgebraInvolution.finiteEvaluation v)
              (u.unop.val.1 : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) := by
  let := auxiliaryStarRing D C
  intro q e he eta u hframe y
  have hconj (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) :
      rationalHomMap (Over.mk s) (fun _ => True) (RationalAlgebraAction.hom0 e.hom)
          (eta.1 x) = eta.1 (x * (u.unop.val.1 : (Global.FiniteAdeles ℚ) ⊗[ℚ] A)) :=
    congrArg (fun xi : Frame => xi.1 x) hframe
  have hcoord :
      eta.1.symm (rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.hom0 e.hom) y) =
          eta.1.symm y * (u.unop.val.1 : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) := by
    apply eta.1.injective
    simpa only [LinearEquiv.apply_symm_apply] using hconj (eta.1.symm y)
  change AlgebraInvolution.changeCoefficients (AlgebraInvolution.finiteEvaluation v) _ = _
  rw [hcoord, map_mul]
  rfl

omit hμfin hμet in
/-- If the original frame element is the identity at a finite place, the actual
rational self-isogeny fixes every local frame coordinate there. -/
theorem localFrameCoordinate_fixed_of_local_identity (v : Global.FinitePlace ℚ) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e)
      (eta : Frame) (u : OriginalGroup),
      (letI : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
       frameIsogeny q (RationalAlgebraAction.underlyingIso e)
          (RationalAlgebraAction.intertwines e.hom) he eta =
        right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C)) eta (scalarEquiv u)) →
      D.rationalInvolution.pointsMap (AlgebraInvolution.finiteEvaluation v) u.unop = 1 →
      ∀ y : RationalFull X.actionObj.abelianScheme (Over.mk s),
        localFrameCoordinate D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h s X v eta
            (rationalHomMap (Over.mk s) (fun _ => True)
              (RationalAlgebraAction.hom0 e.hom) y) =
          localFrameCoordinate D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h s X v eta y := by
  let := auxiliaryStarRing D C
  intro q e he eta u hframe hlocal y
  have hcoeff := congrArg
    (fun z : D.rationalInvolution.Points (Global.FiniteCompletion ℚ v) =>
      (z.val.1 : (Global.FiniteCompletion ℚ v) ⊗[ℚ] A)) hlocal
  change AlgebraInvolution.changeCoefficients (AlgebraInvolution.finiteEvaluation v)
    (u.unop.val.1 : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) = 1 at hcoeff
  rw [localFrameCoordinate_frame_isogeny D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h s
    additivity X v q e he eta u hframe y, hcoeff, mul_one]

/-- Conditional on finite order of the actual rational self-isogeny, local
smallness makes all coordinates in an actual extracted frame fixed. -/
theorem exists_localFrameCoordinate_fixed_of_levelIso_fixed
    (U : HarrisLevel D) (v : Global.FinitePlace ℚ)
    (hsmall : D.rationalInvolution.LevelSmallAt U v) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      (let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
       IsOfFinOrder f) →
      ∃ eta : Frame, ∀ y : RationalFull X.actionObj.abelianScheme (Over.mk s),
        localFrameCoordinate D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h s X v eta
            (rationalHomMap (Over.mk s) (fun _ => True)
              (RationalAlgebraAction.hom0 e.hom) y) =
          localFrameCoordinate D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h s X v eta y := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed hfin
  obtain ⟨eta, u, _hu, hframe, hlocal⟩ := exists_localIdentity_frame_of_levelIso_fixed
    D C preservation composition unitCoherence associativity comparison symmetry
    stability square universality compatibility h s hs htor hu additivity X U v hsmall
    a q e he hfixed hfin
  exact ⟨eta, localFrameCoordinate_fixed_of_local_identity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s additivity X v q e he eta u hframe hlocal⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
