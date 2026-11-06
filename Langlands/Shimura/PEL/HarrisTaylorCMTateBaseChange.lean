import Langlands.Shimura.PEL.HarrisTaylorCMTateFunctoriality
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralImageBaseChange
import Langlands.Shimura.PEL.HarrisIntegralNormalizationBaseChange

/-! # Actual base change of full Tate-normalized Harris CM models -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (P : Prerequisites.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "Bases" => AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "NRepAt" X:max a:max =>
  TateNormalizedCMRepresentative D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "NClassesAt" X:max a:max =>
  TateNormalizedCMIsoClass D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "repClassAt" X:max a:max =>
  tateNormalizedCMRepresentativeClass D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "forgetAt" X:max a:max =>
  tateNormalizedCMForget D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "relIffAt" X:max a:max =>
  tateNormalizedCMRelated_iff_class_eq D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "duals" => unpointedPullbackDualData D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "originalPullAt" X:max Y:max f:max a:max =>
  geometricFamilyPointPullback D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality polarizationStability compatibility h htor (f).hom.left
  (X).obj.hom (Y).obj.hom (Over.w (f).hom) (X).property.lieNaturality
  (X).property.torsionUnits (Y).property.torsionUnits (duals f)
  (X).property.pairAdditivity (Y).property.pairAdditivity a

section Pullback

variable {X Y : AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality}
  (f : Y ⟶ X) (a : HarrisGeometricPoint Y.obj.left)

/-- Pull back the actual polarized CM scheme and its integral action, retaining
the original pulled-back orbit and its full Tate normalization. -/
def tateNormalizedCMRepresentativeBaseChange (U : HarrisLevel D)
    (x : (NRepAt X (a.comp f.hom.left)) U) : (NRepAt Y a) U := by
  let := auxiliaryStarRing D C
  let y := integralCMRepresentativeBaseChange D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
    P.universality dualityNaturality polarizationStability f.hom.left compatibility h
    a.hom a.finiteFibers (a.comp f.hom.left).finiteFibers htor
    X.property.torsionUnits Y.property.torsionUnits (duals f) X.obj.hom
    X.property.lieNaturality U x.toIntegralCMRepresentative
  exact {
    data := y.data
    condition := by simpa only [Over.w f.hom] using y.condition
    restriction := y.restriction
    normalized := (harrisIntegralLevelCondition_levelDataBaseChange D C P
      dualityNaturality polarizationStability f.hom.left compatibility h a.hom
      a.finiteFibers (a.comp f.hom.left).finiteFibers htor X.property.torsionUnits
      Y.property.torsionUnits (duals f) U x.data).mpr x.normalized }

local notation "pullRep" => tateNormalizedCMRepresentativeBaseChange D C P
  dualityNaturality polarizationStability compatibility h htor

/-- Forgetting the actual normalized pullback gives exactly the original
CM pullback, including its commuting structure triangle. -/
@[simp] theorem tateNormalizedCMRepresentativeClass_baseChange (U : HarrisLevel D)
    (x : (NRepAt X (a.comp f.hom.left)) U) :
    (repClassAt Y a) (pullRep f a U x) =
      (originalPullAt X Y f a).app U ((repClassAt X (a.comp f.hom.left)) x) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [geometricFamilyPointPullback, classTowerBaseChangeAlong_eq D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    P.square P.universality dualityNaturality polarizationStability compatibility h htor
    f.hom.left X.obj.hom Y.obj.hom (a.comp f.hom.left).hom a.hom (Over.w f.hom)
    rfl (a.comp f.hom.left).finiteFibers a.finiteFibers X.property.lieNaturality
    X.property.torsionUnits Y.property.torsionUnits (duals f) X.property.pairAdditivity
    Y.property.pairAdditivity (a.comp f.hom.left).finiteFibers]
  simp only [NatTrans.comp_app, types_comp, Function.comp_apply,
    TypeCat.ofHom_apply, classTowerPresentationEq_app,
    classPresentationEq_val_val, ambientClassPointEq, classTowerBaseChange]
  rfl

/-- Actual normalized pullback preserves the unchanged rational-isogeny relation. -/
theorem tateNormalizedCMRelated_baseChange (U : HarrisLevel D)
    (x y : (NRepAt X (a.comp f.hom.left)) U)
    (hxy : TateNormalizedCMRelated D C P X compatibility h (a.comp f.hom.left).hom
      (a.comp f.hom.left).finiteFibers htor x y) :
    TateNormalizedCMRelated D C P Y compatibility h a.hom a.finiteFibers htor
      (pullRep f a U x) (pullRep f a U y) := by
  apply (relIffAt Y a) _ _ |>.mpr
  simp only [tateNormalizedCMRepresentativeClass_baseChange]
  exact congrArg ((originalPullAt X Y f a).app U)
    (((relIffAt X (a.comp f.hom.left)) x y).mp hxy)

/-- Base change on normalized classes is induced by the actual model pullback. -/
def tateNormalizedCMClassBaseChange (U : HarrisLevel D) :
    (NClassesAt X (a.comp f.hom.left)) U → (NClassesAt Y a) U :=
  Quotient.map (pullRep f a U)
    (tateNormalizedCMRelated_baseChange D C P dualityNaturality polarizationStability
      compatibility h htor f a U)

local notation "pull" => tateNormalizedCMClassBaseChange D C P
  dualityNaturality polarizationStability compatibility h htor

/-- The new quotient pullback lies over the literal original CM pullback. -/
@[simp] theorem tateNormalizedCMForget_baseChange (U : HarrisLevel D)
    (q : (NClassesAt X (a.comp f.hom.left)) U) :
    (forgetAt Y a) (pull f a U q) =
      (originalPullAt X Y f a).app U ((forgetAt X (a.comp f.hom.left)) q) := by
  refine Quotient.inductionOn q ?_
  intro x
  exact tateNormalizedCMRepresentativeClass_baseChange D C P dualityNaturality
    polarizationStability compatibility h htor f a U x

end Pullback

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
