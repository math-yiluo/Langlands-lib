import Langlands.Shimura.PEL.HarrisIntegralFrameReduction
import Langlands.Shimura.PEL.HarrisIntegralOrderDescent

/-! # Actual integral order operators in normalized Harris frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C

/-- Left multiplication by the order element, restricted to the fixed integral
adelic source. -/
def harrisIntegralSourceOrderOperator (a : O) : Λf →+ Λf where
  toFun v := ⟨D.harrisIntegralAdeleOrderAction C a v,
    D.harrisIntegralAdeleOrderAction_mem C a v.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' v w := Subtype.ext (map_add (D.harrisIntegralAdeleOrderAction C a) v.val w.val)

variable (P : Prerequisites.{0}) {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation "Restriction" => PolarizedWeilLevel.IntegralActionRestriction
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality
local notation "full" => harrisIntegralFrameFull D C P compatibility h s
local notation "T" => Over.mk s
local notation "PAll" => (fun _ : ℕ => True)

/-- The normalized full integral frame transports the action of an actual integral
endomorphism agreeing with the rational order action. -/
theorem harrisIntegralFrameFull_order (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (i : letI := auxiliaryStarRing D C; Restriction O X) (a : O) (v : Λf) :
    letI := auxiliaryStarRing D C
    GroupScheme.Tate.map T PAll (groupHom (i.action a).asHom) (full X eta hn v) =
      full X eta hn (harrisIntegralSourceOrderOperator D C a v) := by
  let := auxiliaryStarRing D C
  apply GroupScheme.Tate.full_toRational_injective X.actionObj.abelianScheme.toGrp T
  rw [← GroupScheme.Tate.rationalMap_toRational, harrisIntegralFrameFull_toRational,
    harrisIntegralFrameFull_toRational]
  change AbelianScheme.Tate.rationalMap T PAll (i.action a).asHom (eta.val v) =
    eta.val (D.harrisIntegralAdeleOrderAction C a v)
  rw [← Tate.rationalHomMap_ofHom]
  refine (congrArg (fun f : Rationalization.Hom X.actionObj.abelianScheme
    X.actionObj.abelianScheme => Tate.rationalHomMap T PAll f (eta.val v)) (i.agrees a)).trans ?_
  exact (harrisIntegralFrame_order D C P compatibility h s X eta a v).symm

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
