import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficientDiagram
import Langlands.Shimura.Coefficients.VaryingCoverLocalTrivialization
import Langlands.Shimura.Coefficients.VaryingSystemCoverChange

/-! # Associated full Harris coefficient systems on exact geometric CM levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients

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

open Langlands.AlgebraicGeometry

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "Xbar" => Functor.obj (geometricSchemes q) U
local notation "Jbar" => Scheme.smallEtaleTopology Xbar
local notation "R" => HarrisCoefficientIntegers K p
local notation "groups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "coefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "torsor" k => cmHarrisGeometricCoefficientTorsor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k

/-- The full integral-scalar Harris coefficient system associated to the exact
geometric full-kernel covers, with the proved inverse-cover transitions. -/
def cmHarrisGeometricAssociatedCoefficientSystem :
    ℕᵒᵖ ⥤ Sheaf Jbar (ModuleCat.{0} R) :=
  etaleAssociatedVaryingSystem Xbar covers coverProperty coefficients

local notation "system" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Each component is associated to its existing exact geometric coefficient torsor. -/
@[simp] theorem cmHarrisGeometricAssociatedCoefficientSystem_obj (k : ℕᵒᵖ) :
    (system).obj k =
      (etaleAssociatedFunctor Xbar (torsor k.unop).val).obj ((coefficients).action k) := rfl

/-- The transition uses original coefficient reduction and the inverse comparison
for the exact geometric forgetting map. -/
@[simp] theorem cmHarrisGeometricAssociatedCoefficientSystem_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f =
      (etaleAssociatedReduction Xbar covers f).app coefficients ≫
        (etaleAssociatedComparisonIso Xbar covers coverProperty f).inv.app coefficients := rfl

/-- The comparison leg is invertible for every actual geometric cover transition. -/
theorem cmHarrisGeometricAssociatedCoefficientSystem_comparison_isIso
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    IsIso ((etaleAssociatedComparison Xbar covers f).app coefficients) :=
  etaleAssociatedComparison_app_isIso Xbar covers coverProperty f coefficients

/-- The comparison recovers exactly the original full coefficient reduction. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSystem_map_comparison
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f ≫ (etaleAssociatedComparison Xbar covers f).app coefficients =
      (etaleAssociatedReduction Xbar covers f).app coefficients :=
  etaleAssociatedTransition_comparison Xbar covers coverProperty f coefficients

/-- Include the associated sheaf in coefficient-valued sections on the same cover. -/
def cmHarrisGeometricAssociatedCoefficientSystemInclusion (k : ℕᵒᵖ) :
    (system).obj k ⟶
      (productSheaf Jbar ((covers).obj.obj k)).obj
        ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) :=
  etaleAssociatedInclusion Xbar ((covers).action k) ((coefficients).action k)

local notation "inc" => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

instance cmHarrisGeometricAssociatedCoefficientSystemInclusion_mono (k : ℕᵒᵖ) :
    Mono ((inc) k) :=
  etaleAssociatedInclusion_mono Xbar ((covers).action k) ((coefficients).action k)

local notation "constantAction" k =>
  Functor.obj (Functor.mapAction (constantSheaf Jbar (ModuleCat.{0} R))
    ((groups).obj k)) ((coefficients).action k)

/-- Sections satisfy the diagonal coefficient and inverse-right deck invariance. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSystemInclusion_invariant
    (k : ℕᵒᵖ) (g : (groups).obj k) :
    (inc) k ≫ (diagonal Jbar ((covers).action k) (constantAction k)).ρ g = (inc) k :=
  inclusion_invariant Jbar ((covers).action k) (constantAction k) g

/-- Original coefficient reduction commutes with pullback along the exact
geometric forgetting map on invariant sections. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSystem_map_inclusion
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f ≫ (inc) j ≫
        coverPullback Jbar ((covers).obj.map f)
          ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj j)) =
      (inc) i ≫ (productSheaf Jbar ((covers).obj.obj i)).map
        ((constantSheaf Jbar (ModuleCat.{0} R)).map ((coefficients).obj.map f)) :=
  etaleAssociatedTransition_inclusion Xbar covers coverProperty f coefficients

/-- This equation determines every geometric coefficient transition uniquely. -/
theorem cmHarrisGeometricAssociatedCoefficientSystem_map_unique
    {i j : ℕᵒᵖ} (f : i ⟶ j)
    (a : (system).obj i ⟶ (system).obj j)
    (ha : a ≫ (inc) j ≫
        coverPullback Jbar ((covers).obj.map f)
          ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj j)) =
      (inc) i ≫ (productSheaf Jbar ((covers).obj.obj i)).map
        ((constantSheaf Jbar (ModuleCat.{0} R)).map ((coefficients).obj.map f))) :
    a = (system).map f := by
  apply etaleAssociatedTransition_hom_ext Xbar covers coverProperty f coefficients
  exact ha.trans (cmHarrisGeometricAssociatedCoefficientSystem_map_inclusion D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    q U ρ p m hm existence geometry hRigid f).symm

local notation "localizeOn" Z => (Jbar).overPullback (ModuleCat.{0} R) Z

/-- The associated coefficient sheaf trivializes by invariant evaluation along
any actual map into its exact geometric coefficient cover. -/
def cmHarrisGeometricAssociatedCoefficientTrivializationAlong (k : ℕᵒᵖ)
    {Z : (Xbar).Etale} (a : Z ⟶ (covers).obj.obj k) :
    (localizeOn Z).obj ((system).obj k) ≅
      (localizeOn Z).obj
        ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) :=
  etaleAssociatedTrivializationAlong Xbar covers coverProperty coefficients k a

/-- The trivialization uses exactly the invariant-section evaluation map. -/
@[simp] theorem cmHarrisGeometricAssociatedCoefficientTrivializationAlong_hom
    (k : ℕᵒᵖ) {Z : (Xbar).Etale} (a : Z ⟶ (covers).obj.obj k) :
    (cmHarrisGeometricAssociatedCoefficientTrivializationAlong D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      q U ρ p m hm existence geometry hRigid k a).hom =
      etaleAssociatedEvaluationAlong Xbar covers coefficients k a := rfl

/-- Evaluation commutes with every exact geometric cover transition and the
original coefficient reduction. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSystem_evaluationAlong
    {i j : ℕᵒᵖ} (f : i ⟶ j) {Z : (Xbar).Etale} (a : Z ⟶ (covers).obj.obj i) :
    (localizeOn Z).map ((system).map f) ≫
        etaleAssociatedEvaluationAlong Xbar covers coefficients j (a ≫ (covers).obj.map f) =
      etaleAssociatedEvaluationAlong Xbar covers coefficients i a ≫
        (localizeOn Z).map
          ((constantSheaf Jbar (ModuleCat.{0} R)).map ((coefficients).obj.map f)) :=
  etaleAssociatedTransition_evaluationAlong Xbar covers coverProperty coefficients f a

/-- All exponents reachable from k, localized on its exact geometric cover. -/
def cmHarrisGeometricAssociatedCoefficientSourceSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((Jbar).over ((covers).obj.obj k)) (ModuleCat.{0} R) :=
  Under.forget k ⋙ system ⋙ localizeOn ((covers).obj.obj k)

/-- The original full-lattice reduction diagram, made constant and localized
on the same exact geometric source cover. -/
def cmHarrisGeometricConstantCoefficientSourceSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((Jbar).over ((covers).obj.obj k)) (ModuleCat.{0} R) :=
  etaleConstantSourceSystem Xbar covers k coefficients

/-- Invariant evaluation simultaneously trivializes the reachable geometric
coefficient diagram with its original full-lattice reduction maps. -/
def cmHarrisGeometricAssociatedCoefficientSourceTrivialization (k : ℕᵒᵖ) :
    cmHarrisGeometricAssociatedCoefficientSourceSystem D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k ≅
    cmHarrisGeometricConstantCoefficientSourceSystem D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k :=
  etaleAssociatedSourceTrivialization Xbar covers coverProperty k coefficients

local notation "sourceTrivialization" k =>
  cmHarrisGeometricAssociatedCoefficientSourceTrivialization D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k

/-- Each component evaluates along the original geometric forgetting map. -/
@[simp] theorem cmHarrisGeometricAssociatedCoefficientSourceTrivialization_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    (sourceTrivialization k).hom.app i =
      etaleAssociatedEvaluationAlong Xbar covers coefficients i.right
        ((covers).obj.map i.hom) := rfl

/-- Under this single-cover trivialization, every transition is the original
full-lattice coefficient reduction. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceTrivialization_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    (localizeOn ((covers).obj.obj k)).map ((system).map f.right) ≫
        (sourceTrivialization k).hom.app j =
      (sourceTrivialization k).hom.app i ≫
        (localizeOn ((covers).obj.obj k)).map
          ((constantSheaf Jbar (ModuleCat.{0} R)).map ((coefficients).obj.map f.right)) :=
  (sourceTrivialization k).hom.naturality f

local notation "fieldProjection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "π" => (fieldProjection).app U
local notation "originalCovers" => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "originalProperty" => cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "pulledCovers" => (etaleTorsorDiagramPullback π groups).obj originalCovers
local notation "pulledProperty" =>
  etaleTorsorDiagramPullback_isFiniteGeometricTorsor π groups originalCovers originalProperty
local notation "coverIso" => cmHarrisGeometricCoefficientEtaleDiagramPullbackIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

/-- Canonical comparison of the whole associated geometric system with the
system associated to the generic pulled-back original covers. -/
def cmHarrisGeometricAssociatedCoefficientSystemCoverIso :
    etaleAssociatedVaryingSystem Xbar pulledCovers pulledProperty coefficients ≅ system :=
  (etaleAssociatedVaryingSystemCoverIso Xbar R coverProperty pulledProperty coverIso).app
    coefficients

local notation "systemIso" => cmHarrisGeometricAssociatedCoefficientSystemCoverIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

/-- The forward map pulls invariant sections along the original cartesian
comparison, with the identity on the unchanged coefficient representation. -/
@[simp] theorem cmHarrisGeometricAssociatedCoefficientSystemCoverIso_hom_app
    (k : ℕᵒᵖ) :
    (systemIso).hom.app k =
      etaleCrossCoverMap Xbar (MonoidHom.id ((groups).obj k))
        ((EquivariantDiagram.evaluation k).map (coverIso).hom)
        (𝟙 ((coefficients).action k)) := rfl

@[simp] theorem cmHarrisGeometricAssociatedCoefficientSystemCoverIso_inv_app
    (k : ℕᵒᵖ) :
    (systemIso).inv.app k =
      etaleCrossCoverMap Xbar (MonoidHom.id ((groups).obj k))
        ((EquivariantDiagram.evaluation k).map (coverIso).inv)
        (𝟙 ((coefficients).action k)) := rfl

/-- This is a comparison of all specified transitions, with the same original
full coefficient reductions on both sides. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSystemCoverIso_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (etaleAssociatedVaryingSystem Xbar pulledCovers pulledProperty coefficients).map f ≫
        (systemIso).hom.app j =
      (systemIso).hom.app i ≫ (system).map f :=
  (systemIso).hom.naturality f

/-- The forward comparison preserves the actual invariant inclusions and
pulls only the cover coordinate along the canonical cartesian map. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSystemCoverIso_hom_inclusion
    (k : ℕᵒᵖ) :
    (systemIso).hom.app k ≫ (inc) k =
      etaleAssociatedInclusion Xbar ((pulledCovers).action k) ((coefficients).action k) ≫
        coverPullback Jbar ((coverIso).hom.hom.app k)
          ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) := by
  rw [cmHarrisGeometricAssociatedCoefficientSystemCoverIso_hom_app]
  exact etaleCrossCoverMap_identity_inclusion Xbar R
    (A := (pulledCovers).action k) (B := (covers).action k)
    (MonoidHom.id ((groups).obj k))
    ((EquivariantDiagram.evaluation k).map (coverIso).hom) ((coefficients).action k)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
