import Langlands.Shimura.PEL.HarrisTaylorCMFrameMultiplier
import Langlands.Global.AdelicGroupNormOneFunctorial

/-! # Compactness controls rational multipliers of actual Harris frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Global

/-- A rational finite idele occurring under a continuous character of a compact
subgroup has rational absolute value one. -/
theorem abs_rat_eq_one_of_compact_character
    {G : Type*} [Group G] [TopologicalSpace G]
    (χ : G →ₜ* FiniteIdeles ℚ) (K : Subgroup G) (hK : IsCompact (K : Set G))
    {u : G} (hu : u ∈ K) (q : ℚˣ)
    (hq : χ u = Units.map (algebraMap ℚ (FiniteAdeles ℚ)) q) :
    |(q : ℚ)| = 1 := by
  have hn := continuousMonoidHom_eq_one_on_compactSubgroup
    ((IdeleAbsoluteValue.finite ℚ).comp χ) K hK hu
  have hnReal := congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) hn
  change (IdeleAbsoluteValue.finiteValue ℚ (χ u) : ℝ) = 1 at hnReal
  rw [hq, IdeleAbsoluteValue.finiteValue_eq_norm] at hnReal
  change ‖algebraMap ℚ (FiniteAdeles ℚ) (q : ℚ)‖ = 1 at hnReal
  rw [NumberField.FiniteAdeleRing.coe_norm_eq_inv_abs_norm q.ne_zero,
    Algebra.norm_self] at hnReal
  have hqRat : |(q : ℚ)|⁻¹ = 1 := by exact_mod_cast hnReal
  exact inv_eq_one.mp hqRat

end Langlands.Global

namespace Langlands.Shimura.AlgebraInvolution

variable {A : Type*} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)

/-- The multiplier character on the opposite original Harris group. The target
is commutative, so reversal of multiplication causes no change. -/
def oppositeFiniteAdelicMultiplier : σ.FiniteAdelicPointsᵐᵒᵖ →ₜ* Global.FiniteIdeles ℚ where
  toFun u := Points.multiplier σ (Global.FiniteAdeles ℚ) u.unop
  map_one' := _root_.map_one _
  map_mul' u v := by
    change Points.multiplier σ (Global.FiniteAdeles ℚ) (v.unop * u.unop) = _
    rw [_root_.map_mul, mul_comm]
  continuous_toFun := (Points.continuous_multiplier σ (Global.FiniteAdeles ℚ)).comp
    MulOpposite.continuous_unop

@[simp] theorem oppositeFiniteAdelicMultiplier_apply (u : σ.FiniteAdelicPointsᵐᵒᵖ) :
    σ.oppositeFiniteAdelicMultiplier u =
      Points.multiplier σ (Global.FiniteAdeles ℚ) u.unop := rfl

/-- A diagonal rational multiplier in a compact original level is a sign. -/
theorem abs_multiplier_eq_one_of_mem_compact
    (K : Subgroup σ.FiniteAdelicPointsᵐᵒᵖ)
    (hK : IsCompact (K : Set σ.FiniteAdelicPointsᵐᵒᵖ))
    {u : σ.FiniteAdelicPointsᵐᵒᵖ} (hu : u ∈ K) (q : ℚˣ)
    (hq : Points.multiplier σ (Global.FiniteAdeles ℚ) u.unop =
      Units.map (algebraMap ℚ (Global.FiniteAdeles ℚ)) q) :
    |(q : ℚ)| = 1 :=
  Global.abs_rat_eq_one_of_compact_character σ.oppositeFiniteAdelicMultiplier K hK hu q hq

end Langlands.Shimura.AlgebraInvolution

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
/-- Compactness of the original level makes the rational geometric multiplier
in an actual frame equation have absolute value one. -/
theorem abs_multiplier_eq_one_of_original_level_frame (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e)
      (eta : Frame) (u : OriginalGroup), u ∈ U.subgroup →
      (letI : MulAction (ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C))ᵐᵒᵖ Frame := rightAction
       frameIsogeny q (RationalAlgebraAction.underlyingIso e)
          (RationalAlgebraAction.intertwines e.hom) he eta =
        right (G := ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ)
          (D.harrisHodgePELForm C)) eta (scalarEquiv u)) →
      |(q : ℚ)| = 1 := by
  let := auxiliaryStarRing D C
  intro q e he eta u hu hframe
  exact D.rationalInvolution.abs_multiplier_eq_one_of_mem_compact U.subgroup U.isCompact
    hu q (originalElement_multiplier_of_frame_isogeny D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h s additivity X q e he eta u hframe)

/-- An actual fixed orbit at any original Harris level forces its rational
polarization multiplier to have absolute value one. -/
theorem abs_multiplier_eq_one_of_levelIso_fixed (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      |(q : ℚ)| = 1 := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed
  obtain ⟨eta, u, hu, hframe⟩ := exists_frame_original_element_of_levelIso_fixed
    D C preservation composition unitCoherence associativity comparison symmetry
    stability square universality compatibility h s hs htor hu additivity X U a q e he hfixed
  exact abs_multiplier_eq_one_of_original_level_frame D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s additivity X U q e he eta u hu hframe

/-- Once positivity of the actual rational multiplier is established, a fixed
original level orbit forces that multiplier to be one. -/
theorem multiplier_eq_one_of_levelIso_fixed_of_pos (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
      0 < (q : ℚ) → q = 1 := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed hpos
  apply Units.ext
  have habs := abs_multiplier_eq_one_of_levelIso_fixed D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h s hs htor hu additivity X U a q e he hfixed
  simpa only [abs_of_pos hpos, Units.val_one] using habs

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
