import Langlands.Shimura.PEL.HarrisTaylorCMFixedFrameWitness

/-! # Multiplier comparison for actual fixed Harris frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.FormIso

variable {R B V W M : Type*} [CommRing R] [Ring B]
  [AddCommGroup V] [Module R V] [Module B V]
  [AddCommGroup W] [Module R W] [Module B W]
  [AddCommGroup M] [Module R M]
  {ψ : V →ₗ[R] V →ₗ[R] R} {φ : W →ₗ[R] W →ₗ[R] M}

/-- A value-one source form identifies the source and target multipliers
through an actual compatible frame and its intertwining equation. -/
theorem multiplier_eq_of_intertwines (hψ : ∃ x y, ψ x y = 1)
    (eta : FormIso B ψ φ) (g : bilinearSimilitudes B ψ)
    (f : W → W) (c : R)
    (hscale : ∀ x y, φ (f x) (f y) = c • φ x y)
    (hconj : ∀ x, f (eta.1 x) = eta.1 (g.val.1 x)) :
    (g.val.2 : R) = c := by
  obtain ⟨x, y, hxy⟩ := hψ
  obtain ⟨t, ht⟩ := eta.2
  have heq := hscale (eta.1 x) (eta.1 y)
  rw [hconj, hconj, ht, ht, g.property, hxy, mul_one] at heq
  have hlinear : c • t 1 = t c := by
    rw [← t.map_smul]
    simp only [smul_eq_mul, mul_one]
  rw [hlinear] at heq
  exact t.injective heq

end Langlands.Shimura.PEL.FormIso

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
/-- The geometric polarization multiplier agrees with the multiplier of the
original Harris element in an actual fixed-frame equation. -/
theorem originalElement_multiplier_of_frame_isogeny :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e)
      (eta : Frame) (u : OriginalGroup),
      (letI : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
       frameIsogeny q (RationalAlgebraAction.underlyingIso e)
          (RationalAlgebraAction.intertwines e.hom) he eta =
        right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C)) eta (scalarEquiv u)) →
      AlgebraInvolution.Points.multiplier D.rationalInvolution
          (Global.FiniteAdeles ℚ) (MulOpposite.unop u) =
        Units.map (algebraMap ℚ (Global.FiniteAdeles ℚ)) q := by
  let := auxiliaryStarRing D C
  intro q e he eta u hframe
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  let := finiteAdeleAlgebraModule X.actionObj.abelianScheme (Over.mk s)
    (fun _ => True) h X.actionObj.action
  let := GroupScheme.Tate.finiteAdeleModule X.actionObj.abelianScheme.toGrp
    (Over.mk s) (fun _ => True) h
  let := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤)
    (fun _ => True) h
  let : IsSimpleRing A := D.simple
  let g := scalarEquiv u
  let f := rationalHomMap (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.hom0 e.hom)
  apply Units.ext
  change (g.val.2 : Global.FiniteAdeles ℚ) =
    algebraMap ℚ (Global.FiniteAdeles ℚ) (q : ℚ)
  apply FormIso.multiplier_eq_of_intertwines
    ((hodgeRationalPELConditions D C).baseChange_attains_one (Global.FiniteAdeles ℚ))
    eta g f _
  · intro x y
    change adelicWeilAlongHomBilinearMap preservation composition unitCoherence
        associativity comparison symmetry stability X.hasDual X.geometry X.inversePoincare
        X.evaluation compatibility (Over.mk s) X.polarization (fun _ => True) h
        (rationalHomMap (Over.mk s) (fun _ => True)
          (RationalAlgebraAction.hom0 e.hom) x)
        (rationalHomMap (Over.mk s) (fun _ => True)
          (RationalAlgebraAction.hom0 e.hom) y) =
      TateTwist.Divisibility.finiteAdeleAction Γ((Over.mk s).left, ⊤) (fun _ => True) h
        (algebraMap ℚ (Global.FiniteAdeles ℚ) (q : ℚ))
        (adelicWeilAlongHomBilinearMap preservation composition unitCoherence
          associativity comparison symmetry stability X.hasDual X.geometry X.inversePoincare
          X.evaluation compatibility (Over.mk s) X.polarization (fun _ => True) h x y)
    simp only [adelicWeilAlongHomBilinearMap_apply,
      TateTwist.Divisibility.finiteAdeleAction_diagonal]
    exact rationalWeilAlongHomBilinearMap_rationalHom_similitude preservation composition
      unitCoherence associativity comparison symmetry stability X.hasDual X.hasDual
      X.geometry X.geometry X.inversePoincare X.evaluation X.inversePoincare X.evaluation
      (additivity X X) X.polarization X.polarization compatibility rationalWeilFunctoriality
      (Over.mk s) (fun _ => True) (q : ℚ) (RationalAlgebraAction.hom0 e.hom) he x y
  · intro x
    exact congrArg (fun xi : Frame => xi.1 x) hframe

/-- An actual original level frame witness with the geometric multiplier
identified in the original Harris group. -/
def OriginalLevelMultiplierFrameWitness (U : HarrisLevel D) :
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
        (D.harrisHodgePELForm C)) eta (scalarEquiv u) ∧
    AlgebraInvolution.Points.multiplier D.rationalInvolution
        (Global.FiniteAdeles ℚ) (MulOpposite.unop u) =
      Units.map (algebraMap ℚ (Global.FiniteAdeles ℚ)) q

/-- A fixed actual level orbit supplies an original-group witness with its
multiplier equal to the diagonal geometric polarization multiplier. -/
theorem exists_multiplier_frame_of_levelIso_fixed (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      OriginalLevelMultiplierFrameWitness D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility
        h s additivity X U q e he := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed
  obtain ⟨eta, u, hu, hframe⟩ := exists_frame_original_element_of_levelIso_fixed
    D C preservation composition unitCoherence associativity comparison symmetry
    stability square universality compatibility h s hs htor hu additivity X U a q e he hfixed
  exact ⟨eta, u, hu, hframe, originalElement_multiplier_of_frame_isogeny D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality compatibility h s additivity X q e he eta u hframe⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
