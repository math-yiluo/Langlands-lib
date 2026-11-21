import Langlands.Shimura.PEL.HarrisNormalizedPolarization
import Langlands.AbelianScheme.PolarizedFiniteLevel.PrimitivePolarizationTransport
import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison
import Langlands.Shimura.PEL.PolarizedWeilOrderModel

/-! # Invariance of primitive Harris polarizations under isomorphism -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "G" => ScalarExtensionSimilitudePoints A A Af (D.harrisHodgePELForm C)
local notation "Stab" => (harrisIntegralAdeleStabilizer D C : Subgroup G)
local notation "op" => ScalarExtensionSimilitudePoints.operator
local notation "K" => harrisIntegralAdeleCongruence D C
local notation "multiples" => harrisIntegralSourceMultiples D C
local notation "integralOp" => harrisIntegralSourceOperator D C
local notation "reduceOp" => harrisIntegralSourceReduction D C

local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (X).hasDual (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization
  h (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation:max "Full" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation:max "toRat" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True)
local notation:max "rat_injective" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.full_toRational_injective (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation:max "Level" X:max m:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Level (X).actionObj.abelianScheme.toGrp (Over.mk s) (m : ℕ)
local notation:max "eval" X:max m:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.evaluation (X).actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True) m

local notation "L" => D.harrisHodgePELIntegralLattice C
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "polOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).polarization
local notation:max "DOf" X:max =>
  letI := auxiliaryStarRing D C
  dualAbelianSchemeFromEvaluation (X).actionObj.abelianScheme (X).hasDual (X).geometry
    P.preservation (X).inversePoincare (X).evaluation P.stability P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry

local notation:max "pullZ" X:max Y:max =>
  letI := auxiliaryStarRing D C
  integralDualPullbackHom P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability (X).hasDual (Y).hasDual (X).geometry (Y).geometry
    (X).inversePoincare (X).evaluation (Y).inversePoincare (Y).evaluation

local notation:max "WOf" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PolarizedAction.dualWitness P X

omit [QuasiSeparatedSpace S] in
/-- The Harris dual pullback along an isomorphism is the published transport for the
published dual witnesses of the two polarized actions. -/
theorem harrisDualPullback_eq_transportMap (X Y : PObj) (g : BOf X ≅ BOf Y)
    (lam : BOf Y ⟶ DOf Y) :
    pullZ X Y g.hom lam = DualWitness.transportMap P g (WOf X) (WOf Y) lam := rfl

section Geometric

variable [IsLocallyNoetherian S] [ConnectedSpace S] [IsAlgClosed Ω]
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hpos : PolarizationRayPositivityStatement.{0})

omit [IsLocallyNoetherian S] [ConnectedSpace S] in
/-- The primitive polarization of a polarized Harris action that has a normalized frame at
the algebraically closed point. The choice does not depend on the frame, since only the
existence statement enters, and it is unique on a connected base. -/
def harrisPrimitivePolarizationOf (X : PObj) (eta : Frame X) (hn : Normalized X eta) :
    BOf X ⟶ DOf X :=
  Classical.choose (exists_harrisPrimitivePolarization D C P compatibility h s hu X eta hn)

omit [IsLocallyNoetherian S] [ConnectedSpace S] in
theorem harrisPrimitivePolarizationOf_spec (X : PObj) (eta : Frame X)
    (hn : Normalized X eta) :
    HarrisPrimitivePolarization D C P X
      (harrisPrimitivePolarizationOf D C P compatibility h s hu X eta hn) :=
  Classical.choose_spec (exists_harrisPrimitivePolarization D C P compatibility h s hu X eta hn)

include htor in
/-- Every primitive polarization of `X` is the chosen one. -/
theorem harrisPrimitivePolarizationOf_eq (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    {lam : BOf X ⟶ DOf X} (hlam : HarrisPrimitivePolarization D C P X lam) :
    harrisPrimitivePolarizationOf D C P compatibility h s hu X eta hn = lam :=
  harrisPrimitivePolarization_unique D C P s hu htor X
    (harrisPrimitivePolarizationOf_spec D C P compatibility h s hu X eta hn) hlam

omit [QuasiSeparatedSpace S] in
include hpos htor hu s in
/-- If the Harris dual pullback of the polarization of `Y` along an isomorphism is an
integral rational multiple of the polarization of `X`, then it carries the primitive
polarization of `Y` to that of `X`. -/
theorem harrisPrimitivePolarization_pullback (X Y : PObj) (g : BOf X ≅ BOf Y) (q : ℚ)
    (d : Rationalization.IntegralMultipleData (pullZ X Y g.hom (polOf Y)) (polOf X) q)
    (gd : ℕ) (hgd : 0 < gd) (hdim : (BOf X).HasRelativeDimension gd)
    {lamX : BOf X ⟶ DOf X} {lamY : BOf Y ⟶ DOf Y}
    (hX : HarrisPrimitivePolarization D C P X lamX)
    (hY : HarrisPrimitivePolarization D C P Y lamY) :
    pullZ X Y g.hom lamY = lamX := by
  let := auxiliaryStarRing D C
  obtain ⟨hpX, kX, hkX, hlamX⟩ := hX
  obtain ⟨hpY, kY, hkY, hlamY⟩ := hY
  exact DualWitness.transportMap_eq_of_primitive P hpos htor hu s g (WOf X) (WOf Y) gd hgd
    hdim X.isPolarization Y.isPolarization d.left_ne_zero d.equation hpX hpY hkX hkY hlamX
    hlamY

include hpos htor in
/-- The chosen primitive polarizations are compatible with integral rational multiples of
the polarizations along isomorphisms. -/
theorem harrisPrimitivePolarizationOf_pullback (X Y : PObj) (etaX : Frame X)
    (hnX : Normalized X etaX) (etaY : Frame Y) (hnY : Normalized Y etaY) (g : BOf X ≅ BOf Y)
    (q : ℚ) (d : Rationalization.IntegralMultipleData (pullZ X Y g.hom (polOf Y)) (polOf X) q)
    (gd : ℕ) (hgd : 0 < gd) (hdim : (BOf X).HasRelativeDimension gd) :
    pullZ X Y g.hom (harrisPrimitivePolarizationOf D C P compatibility h s hu Y etaY hnY) =
      harrisPrimitivePolarizationOf D C P compatibility h s hu X etaX hnX :=
  harrisPrimitivePolarization_pullback D C P s hu htor hpos X Y g q d gd hgd hdim (harrisPrimitivePolarizationOf_spec D C P compatibility h s hu X etaX hnX)
    (harrisPrimitivePolarizationOf_spec D C P compatibility h s hu Y etaY hnY)

end Geometric

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
