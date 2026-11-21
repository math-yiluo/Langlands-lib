import Langlands.Shimura.PEL.HarrisTaylorCMArtinianGeometricBridge
import Langlands.Shimura.PEL.HarrisTaylorCMDivisionPremiseStatements

/-! # Reduction of division-case Artinian class lifting to geometric lifting -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

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
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "admissible" => AdmissibleCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "tower" => unpointedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor
local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "Lifts" => NormalizedPolarizedActionLiftsAlong D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "evaluate" => unpointedClassTowerEvaluationIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility h htor
local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "dispull" => disconnectedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "componentHom" => componentCMBaseHomTo D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "componentIso" => componentCMBaseInclusionIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "evaluateComponent" => disconnectedClassTowerComponentIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

private theorem classTowerPresentationEq_surjective (T : Bases)
    {q : T.obj.left ⟶ Spec (.of F)} (hq : q = T.obj.hom)
    (a : HarrisGeometricPoint T.obj.left) (U : HarrisLevel D) :
    Function.Surjective ((classTowerPresentationEq D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h htor T.property.torsionUnits T.property.pairAdditivity
      hq (rfl : a.hom = a.hom) a.finiteFibers a.finiteFibers).app U) := by
  subst q
  exact Function.surjective_id

private theorem unpointedClassTowerPullback_surjective_of_normalizedPolarizedActionLifts
    {S T : Bases} (f : T ⟶ S) (a : HarrisGeometricPoint T.obj.left)
    (hLift : Lifts f.hom.left S.obj.hom)
    (hα : Function.Surjective (fundamentalGroupMap f.hom.left a.hom
      (a.comp f.hom.left).hom rfl a.finiteFibers (a.comp f.hom.left).finiteFibers))
    (U : HarrisLevel D) : Function.Surjective ((pull f).app U) := by
  let b := f.hom.left
  let aS := a.comp b
  let duals := unpointedPullbackDualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality f
  let pointPull := geometricFamilyPointPullback D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor b S.obj.hom T.obj.hom (Over.w f.hom)
    S.property.lieNaturality S.property.torsionUnits T.property.torsionUnits duals
    S.property.pairAdditivity T.property.pairAdditivity a
  have hPoint := classBaseChange_surjective_of_normalizedPolarizedActionLifts D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    b S.obj.hom a.hom a.finiteFibers aS.finiteFibers S.property.torsionUnits
    T.property.torsionUnits duals S.property.lieNaturality S.property.pairAdditivity
    T.property.pairAdditivity hLift hα U
  have hPointPull : Function.Surjective (pointPull.app U) := by
    dsimp only [pointPull, geometricFamilyPointPullback]
    rw [classTowerBaseChangeAlong_eq D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b S.obj.hom T.obj.hom aS.hom a.hom
      (Over.w f.hom) rfl aS.finiteFibers a.finiteFibers S.property.lieNaturality
      S.property.torsionUnits T.property.torsionUnits duals S.property.pairAdditivity
      T.property.pairAdditivity aS.finiteFibers]
    simp only [classTowerPresentationEq_refl, Category.id_comp, NatTrans.comp_app]
    exact (classTowerPresentationEq_surjective D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      T (Over.w f.hom) a U).comp hPoint
  let eS := ((evaluate S aS).app U).toEquiv
  let eT := ((evaluate T a).app U).toEquiv
  intro y
  obtain ⟨x, hx⟩ := hPointPull (eT y)
  refine ⟨eS.symm x, eT.injective ?_⟩
  have heval := congrArg (fun k : tower S ⟶ _ => k.app U (eS.symm x))
    (unpointedClassTowerPullback_evaluation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor f a)
  change eT ((pull f).app U (eS.symm x)) = pointPull.app U (eS (eS.symm x)) at heval
  rw [heval, eS.apply_symm_apply, hx]

private theorem disconnectedClassTowerPullback_surjective_of_connected
    {X Y : DisBases} (hX : admissible X.obj) (hY : admissible Y.obj) (f : Y ⟶ X)
    (U : HarrisLevel D) (hSurj : Function.Surjective ((pull
      (ObjectProperty.homMk f.hom : (⟨Y.obj, hY⟩ : Bases) ⟶ (⟨X.obj, hX⟩ : Bases))).app U)) :
    Function.Surjective ((dispull f).app U) := by
  let : ConnectedSpace X.obj.left := hX.connected
  let : ConnectedSpace Y.obj.left := hY.connected
  let f' : (⟨Y.obj, hY⟩ : Bases) ⟶ (⟨X.obj, hX⟩ : Bases) :=
    ObjectProperty.homMk f.hom
  let c := _root_.ConnectedComponents.mk (Classical.arbitrary Y.obj.left)
  let d := componentMap f.hom.left c
  let iX := componentIso X hX d
  let iY := componentIso Y hY c
  let k := componentHom f c d rfl
  have hw : k ≫ iX.hom = iY.hom ≫ f' := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change componentHomTo f.hom.left c d rfl ≫
      (componentInclusionIso X.obj.left d).hom =
      (componentInclusionIso Y.obj.left c).hom ≫ f.hom.left
    rw [componentInclusionIso_hom, componentInclusionIso_hom, componentHomTo_ι]
  have hk : k = (iY.hom ≫ f') ≫ iX.inv := (iX.eq_comp_inv).mpr hw
  have hComponent : Function.Surjective ((pull k).app U) := by
    rw [hk, ← unpointedClassTowerPullback_comp, ← unpointedClassTowerPullback_comp]
    let P := unpointedClassTowerPresheaf D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor
    exact ((P.mapIso iY.op).app U).toEquiv.surjective.comp
      (hSurj.comp ((P.mapIso iX.symm.op).app U).toEquiv.surjective)
  let eX := ((evaluateComponent X d).app U).toEquiv
  let eY := ((evaluateComponent Y c).app U).toEquiv
  intro y
  obtain ⟨z, hz⟩ := hComponent (eY y)
  refine ⟨eX.symm z, eY.injective ?_⟩
  change (pull k).app U (eX (eX.symm z)) = eY y
  rw [eX.apply_symm_apply, hz]

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem admissibleArtinianSpec {B : Type} [CommRing B] [IsLocalRing B]
    [IsArtinianRing B] (β : Spec (.of B) ⟶ Spec (.of F)) : admissible (Over.mk β) := by
  let : ConnectedSpace (Over.mk β).left := by
    change ConnectedSpace (PrimeSpectrum B)
    have h : (Set.univ : Set (PrimeSpectrum B)).Subsingleton :=
      Set.subsingleton_univ_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mpr ⟨Set.univ_nonempty, h.isPreconnected⟩
  let : IsLocallyNoetherian (Over.mk β).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of B)))
  apply (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (Over.mk β)).mpr
  intro Q
  exact ⟨relativeDualSchemeExistence _ Q,
    relativeDualSchemeGeometry _ Q (relativeDualSchemeExistence _ Q)⟩

local notation "test" => specTest D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality
local notation "testMap" => specTestMap D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality
local notation "GeometricLift" => DivisionCMPolarizedActionArtinianLiftingStatement D C
  preservation composition unitCoherence associativity comparison symmetry stability square universality
local notation "ClassLift" => DivisionCMArtinianLiftingStatement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor

/-- Lifting the actual positive polarized actions with their rational isometry
implies the published division-case Artinian lifting criterion for classes. -/
def DivisionCMArtinianLiftingReductionStatement : Prop :=
  GeometricLift → ClassLift

/-- Use normalization reflection, pointed lifting, and the two evaluation
comparisons to lift the original presheaf class at each small level. -/
theorem divisionCMArtinianLifting_of_polarizedActionArtinianLifting :
    DivisionCMArtinianLiftingReductionStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := by
  intro hGeometric hDivision U B' B _ _ _ _ _ _ φ hφ hker β
  let b := Spec.map (CommRingCat.ofHom φ)
  let X := test B' β
  let Y := test B (b ≫ β)
  let f : Y ⟶ X := testMap φ β
  have hX : admissible X.obj := admissibleArtinianSpec D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality β
  have hY : admissible Y.obj := admissibleArtinianSpec D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality (b ≫ β)
  change Function.Surjective ((dispull f).app U.obj)
  apply disconnectedClassTowerPullback_surjective_of_connected D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor hX hY f U.obj
  let Xc : Bases := ⟨X.obj, hX⟩
  let Yc : Bases := ⟨Y.obj, hY⟩
  let f' : Yc ⟶ Xc := ObjectProperty.homMk f.hom
  let a := Classical.arbitrary (HarrisGeometricPoint Yc.obj.left)
  have hLift := normalizedPolarizedActionLiftsAlong_spec_of_geometric D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    hGeometric hDivision φ hφ hker β
  have hα := specArtinianMonodromySurjectivity φ hφ a.hom
    a.finiteFibers (a.comp b).finiteFibers
  exact unpointedClassTowerPullback_surjective_of_normalizedPolarizedActionLifts D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    f' a hLift hα U.obj

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
