import Langlands.Shimura.PEL.HarrisTaylorCMFixedFrameWitness
import Langlands.Shimura.Unitary.SufficientlySmallLevels

/-! # Finite-order transfer and local smallness for actual fixed frames -/

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

/-- An actual fixed-frame witness whose original Harris element is the
identity at the specified finite place. -/
def OriginalLevelLocalIdentityFrameWitness (U : HarrisLevel D)
    (v : Global.FinitePlace ℚ) :
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
    D.rationalInvolution.pointsMap (AlgebraInvolution.finiteEvaluation v)
      (MulOpposite.unop u) = 1

omit hμfin hμet in
/-- A power relation on the actual rational self-isogeny transfers to the
original Harris element in its actual frame equation. -/
theorem originalElement_pow_eq_one_of_frame_isogeny :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e)
      (eta : Frame) (u : OriginalGroup),
      (letI : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
       frameIsogeny q (RationalAlgebraAction.underlyingIso e)
          (RationalAlgebraAction.intertwines e.hom) he eta =
        right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C)) eta (scalarEquiv u)) →
      ∀ m : ℕ, (let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
                f ^ m = 1) →
        u ^ m = 1 := by
  let := auxiliaryStarRing D C
  intro q e he eta u hframe m hm
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  let : IsSimpleRing A := D.simple
  let g := scalarEquiv u
  let f := rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.hom0 e.hom)
  have hconj (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) :
      f (eta.1 x) = eta.1 (g.val.1 x) :=
    congrArg (fun xi : Frame => xi.1 x) hframe
  have hpow (k : ℕ) (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) :
      (f ^ k) (eta.1 x) = eta.1 ((g.val.1 ^ k) x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ']
      change f ((f ^ k) (eta.1 x)) = eta.1 (g.val.1 ((g.val.1 ^ k) x))
      rw [ih, hconj]
  have hfm : f ^ m = 1 := by
    rw [← map_pow, hm, map_one]
  apply (scalarEquiv).injective
  rw [map_pow, map_one]
  apply bilinearSimilitudes.underlying_injective _
    ((hodgeRationalPELConditions D C).baseChange_attains_one (Global.FiniteAdeles ℚ))
  rw [map_pow, map_one]
  ext x
  apply eta.1.injective
  exact (hpow m x).symm.trans (by rw [hfm]; rfl)

omit hμfin hμet in
/-- Finite order of the actual rational self-isogeny gives finite order of
its original Harris frame element. -/
theorem isOfFinOrder_originalElement_of_frame_isogeny :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e)
      (eta : Frame) (u : OriginalGroup),
      (letI : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
       frameIsogeny q (RationalAlgebraAction.underlyingIso e)
          (RationalAlgebraAction.intertwines e.hom) he eta =
        right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C)) eta (scalarEquiv u)) →
      (let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
       IsOfFinOrder f) →
        IsOfFinOrder u := by
  let := auxiliaryStarRing D C
  intro q e he eta u hframe hfin
  obtain ⟨m, hm, hpower⟩ := hfin.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm,
    originalElement_pow_eq_one_of_frame_isogeny D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h s additivity X q e he eta u hframe m hpower⟩

/-- Local smallness kills the local projection of a genuine fixed-orbit
witness when the actual rational self-isogeny has finite order. -/
theorem exists_localIdentity_frame_of_levelIso_fixed
    (U : HarrisLevel D) (v : Global.FinitePlace ℚ)
    (hsmall : D.rationalInvolution.LevelSmallAt U v) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      (let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
       IsOfFinOrder f) →
      OriginalLevelLocalIdentityFrameWitness D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility
        h s additivity X U v q e he := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed hfin
  obtain ⟨eta, u, hu, hframe⟩ := exists_frame_original_element_of_levelIso_fixed
    D C preservation composition unitCoherence associativity comparison symmetry
    stability square universality compatibility h s hs htor hu additivity X U a q e he hfixed
  refine ⟨eta, u, hu, hframe, hsmall u hu ?_⟩
  have hufin := isOfFinOrder_originalElement_of_frame_isogeny D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality compatibility h s additivity X q e he eta u hframe hfin
  obtain ⟨m, hm, hpower⟩ := hufin.exists_pow_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩
  rw [← map_pow, ← MulOpposite.unop_pow, hpower, MulOpposite.unop_one, map_one]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
