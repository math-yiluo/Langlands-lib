import Langlands.Shimura.PEL.HarrisTaylorCMDivisionCriteria

/-! # Pointed reduction of valuative existence for normalized Harris CM classes -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

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

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "disTest" => specTest D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality
local notation "disMap" => specTestMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality

/-- A noetherian domain over the CM field gives an actual connected admissible test. -/
def connectedSpecTest (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (β : Spec (CommRingCat.of B) ⟶ Spec (.of F)) : Bases := by
  refine ⟨Over.mk β, ?_⟩
  let : ConnectedSpace (Over.mk β).left :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of B)))
  let : IsLocallyNoetherian (Over.mk β).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of B)))
  apply (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (Over.mk β)).mpr
  intro B'
  exact ⟨relativeDualSchemeExistence _ B', relativeDualSchemeGeometry _ B' _⟩

local notation "connTest" => connectedSpecTest D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality

/-- The map on connected admissible tests induced by a homomorphism of domains. -/
def connectedSpecTestMap {B' B : Type} [CommRing B'] [CommRing B] [IsDomain B']
    [IsDomain B] [IsNoetherianRing B'] [IsNoetherianRing B] (φ : B' →+* B)
    (β : Spec (CommRingCat.of B') ⟶ Spec (.of F)) :
    connTest B (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ connTest B' β :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl)

local notation "connMap" => connectedSpecTestMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality
local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "pullComp" => unpointedClassTowerPullback_comp D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "disPull" => disconnectedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "connectedIso" => disconnectedClassTowerConnectedIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "inclusionIso" => componentCMBaseInclusionIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "componentHom" => componentCMBaseHomTo D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

private theorem surjective_iff_of_equiv_square {X X' Y Y' : Type*}
    {f : X → Y} {g : X' → Y'} (source : X ≃ X') (target : Y ≃ Y')
    (square : ∀ x, target (f x) = g (source x)) :
    Function.Surjective f ↔ Function.Surjective g := by
  rw [← Function.Surjective.of_comp_iff' target.bijective f,
    ← Function.Surjective.of_comp_iff g source.surjective]
  rw [show target ∘ f = g ∘ source from funext square]

private theorem specTest_map_surjective_iff_unpointed {B' B : Type}
    [CommRing B'] [CommRing B] [IsDomain B'] [IsDomain B] [IsNoetherianRing B']
    [IsNoetherianRing B] (φ : B' →+* B) (β : Spec (CommRingCat.of B') ⟶ Spec (.of F))
    (U : SmallCMLevel D) :
    Function.Surjective ((((moduli).obj U).map (disMap φ β).op)) ↔
      Function.Surjective ((pull (connMap φ β)).app U.obj) := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let X := disTest B' β
  let Y := disTest B (b ≫ β)
  let Xc := connTest B' β
  let Yc := connTest B (b ≫ β)
  let g : Yc ⟶ Xc := connMap φ β
  let r : Y ⟶ X := disMap φ β
  let c : _root_.ConnectedComponents Y.obj.left :=
    _root_.ConnectedComponents.mk (Classical.arbitrary (Spec (CommRingCat.of B)))
  let d := Langlands.AlgebraicGeometry.componentMap r.hom.left c
  let iX : _ ≅ Xc := inclusionIso X Xc.property d
  let iY : _ ≅ Yc := inclusionIso Y Yc.property c
  let f := componentHom r c d rfl
  have commutes : f ≫ iX.hom = iY.hom ≫ g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    have : ConnectedSpace X.obj.left := Xc.property.connected
    have : ConnectedSpace Y.obj.left := Yc.property.connected
    change componentHomTo b c d rfl ≫ (componentInclusionIso X.obj.left d).hom =
      (componentInclusionIso Y.obj.left c).hom ≫ b
    rw [componentInclusionIso_hom, componentInclusionIso_hom]
    exact componentHomTo_ι b c d rfl
  have invCommutes : iY.inv ≫ f = g ≫ iX.inv := by
    calc
      iY.inv ≫ f = (iY.inv ≫ (f ≫ iX.hom)) ≫ iX.inv := by simp
      _ = g ≫ iX.inv := by rw [commutes]; simp
  have pullCommutes : pull f ≫ pull iY.inv = pull iX.inv ≫ pull g := by
    exact (pullComp f iY.inv).trans ((congrArg (fun k => pull k) invCommutes).trans
      (pullComp iX.inv g).symm)
  let eX := (connectedIso X (connTest B' β).property d).app U.obj
  let eY := (connectedIso Y (connTest B (b ≫ β)).property c).app U.obj
  refine surjective_iff_of_equiv_square eX.toEquiv eY.toEquiv (fun x => ?_)
  change (pull iY.inv).app U.obj ((disPull r).app U.obj x c) =
    (pull g).app U.obj ((pull iX.inv).app U.obj (x d))
  rw [disconnectedClassTowerPullback_app_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor r U.obj x c d rfl]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app pullCommutes U.obj) (x d)

local notation "eval" => unpointedClassTowerEvaluationIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility h htor

/-- On spectra of noetherian domains, restriction in the existing small-level presheaf
is surjective exactly when the existing normalized class restriction at a geometric
point of the source of `Spec φ` is surjective. -/
theorem specTest_map_surjective_iff_pointed {B' B : Type} [CommRing B'] [CommRing B]
    [IsDomain B'] [IsDomain B] [IsNoetherianRing B'] [IsNoetherianRing B]
    (φ : B' →+* B) (β : Spec (CommRingCat.of B') ⟶ Spec (.of F))
    (U : SmallCMLevel D) (a : HarrisGeometricPoint (Spec (CommRingCat.of B))) :
    let g := connMap φ β
    let X := connTest B' β
    let Y := connTest B (Spec.map (CommRingCat.ofHom φ) ≫ β)
    Function.Surjective ((((moduli).obj U).map (disMap φ β).op)) ↔
      Function.Surjective ((geometricFamilyPointPullback D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor g.hom.left X.obj.hom
        Y.obj.hom (Over.w g.hom) X.property.lieNaturality X.property.torsionUnits
        Y.property.torsionUnits
        (unpointedPullbackDualData D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality g)
        X.property.pairAdditivity Y.property.pairAdditivity a).app U.obj) := by
  dsimp only
  let g := connMap φ β
  let X := connTest B' β
  let Y := connTest B (Spec.map (CommRingCat.ofHom φ) ≫ β)
  refine (specTest_map_surjective_iff_unpointed D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor φ β U).trans ?_
  refine surjective_iff_of_equiv_square ((eval X (a.comp g.hom.left)).app U.obj).toEquiv
    ((eval Y a).app U.obj).toEquiv (fun x => ?_)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (unpointedClassTowerPullback_evaluation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor g a) U.obj) x

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
