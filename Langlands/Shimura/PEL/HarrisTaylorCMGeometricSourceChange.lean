import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedScalars
import Langlands.Shimura.Coefficients.VaryingCoverSourceChange

/-! # Source changes for exact geometric CM coefficient systems -/

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
open Langlands.Shimura.Coefficients Langlands.Sheaf

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

local notation "schemes" => cmGeometricSchemeTower D C preservation composition
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

local notation "X" => Functor.obj (schemes q) U
local notation "J" => Scheme.smallEtaleTopology X
local notation "R" => HarrisCoefficientIntegers K p
local notation "coefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

local notation "system" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "restrictedSystem" => cmHarrisGeometricAssociatedRestrictedCoefficientSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "systemComparison" => cmHarrisGeometricAssociatedRestrictedCoefficientSystemIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "source" k => cmHarrisGeometricAssociatedCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "restrictedSource" k => cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "constantSource" k => cmHarrisGeometricConstantCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "sourceTrivialization" k => cmHarrisGeometricAssociatedCoefficientSourceTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "restrictedTrivialization" k =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    q U ρ p m hm existence geometry hRigid k
local notation "localize" k => (J).overPullback (ModuleCat.{0} R) ((covers).obj.obj k)

/-- Restrict a whole target-source diagram along the actual geometric forgetting map. -/
def cmHarrisGeometricCoefficientSourceRestriction {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (Under l ⥤ Sheaf ((J).over ((covers).obj.obj l)) (ModuleCat.{0} R)) ⥤
      (Under l ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} R)) :=
  sourceSliceRestriction J (ModuleCat.{0} R) (covers).obj f

/-- Precompose outgoing arrows by the same geometric source transition. -/
def cmHarrisGeometricCoefficientSourceReindex {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (Under k ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} R)) ⥤
      (Under l ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} R)) :=
  sourceSliceReindex J (ModuleCat.{0} R) (covers).obj f

local notation "restrictSource" f => cmHarrisGeometricCoefficientSourceRestriction D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f
local notation "reindexSource" f => cmHarrisGeometricCoefficientSourceReindex D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f

/-- Canonical source change for the integral associated coefficient system. -/
def cmHarrisGeometricAssociatedCoefficientSourceChangeIso
    {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (restrictSource f).obj (source l) ≅ (reindexSource f).obj (source k) :=
  sourceSliceChangeIso J (ModuleCat.{0} R) (covers).obj f system

/-- Canonical source change for the directly associated restricted quotient system. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceChangeIso
    {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (restrictSource f).obj (restrictedSource l) ≅
      (reindexSource f).obj (restrictedSource k) :=
  sourceSliceChangeIso J (ModuleCat.{0} R) (covers).obj f restrictedSystem

/-- Canonical source change for the unchanged full-lattice coefficient diagram. -/
def cmHarrisGeometricConstantCoefficientSourceChangeIso
    {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (restrictSource f).obj (constantSource l) ≅
      (reindexSource f).obj (constantSource k) :=
  etaleConstantSourceChangeIso X covers f coefficients

local notation "sourceChange" f => cmHarrisGeometricAssociatedCoefficientSourceChangeIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f
local notation "restrictedChange" f =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceChangeIso D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    q U ρ p m hm existence geometry hRigid f
local notation "constantChange" f => cmHarrisGeometricConstantCoefficientSourceChangeIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f

/-- The component is the canonical global-to-slice comparison, whose
forward and inverse section maps are identities. -/
@[simp] theorem cmHarrisGeometricAssociatedCoefficientSourceChangeIso_app
    {k l : ℕᵒᵖ} (f : k ⟶ l) (i : Under l) :
    (sourceChange f).app i =
      (overPullbackMapIso J (ModuleCat.{0} R) ((covers).obj.map f)).app
        ((system).obj i.right) := rfl

/-- The component is the canonical global-to-slice comparison, whose
forward and inverse section maps are identities. -/
@[simp] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceChangeIso_app
    {k l : ℕᵒᵖ} (f : k ⟶ l) (i : Under l) :
    (restrictedChange f).app i =
      (overPullbackMapIso J (ModuleCat.{0} R) ((covers).obj.map f)).app
        ((restrictedSystem).obj i.right) := rfl

/-- The component is the canonical global-to-slice comparison, whose
forward and inverse section maps are identities. -/
@[simp] theorem cmHarrisGeometricConstantCoefficientSourceChangeIso_app
    {k l : ℕᵒᵖ} (f : k ⟶ l) (i : Under l) :
    (constantChange f).app i =
      (overPullbackMapIso J (ModuleCat.{0} R) ((covers).obj.map f)).app
        (((coefficients).obj ⋙ constantSheaf J (ModuleCat.{0} R)).obj i.right) := rfl

/-- Identity source change is the standard slice identity comparison,
with the identity law of the exact geometric cover diagram. -/
theorem cmHarrisGeometricAssociatedCoefficientSourceChangeIso_id
    (k : ℕᵒᵖ) (i : Under k) :
    (sourceChange (𝟙 k)).hom.app i =
      ((J).overMapPullbackCongr (ModuleCat.{0} R) ((covers).obj.map_id k)).hom.app
          ((source k).obj i) ≫
        ((J).overMapPullbackId (ModuleCat.{0} R) ((covers).obj.obj k)).hom.app
          ((source k).obj i) :=
  sourceSliceChangeIso_id J (ModuleCat.{0} R) (covers).obj k system i

/-- Successive source changes agree with the direct source change under
the actual slice-composition and geometric cover functor comparisons. -/
theorem cmHarrisGeometricAssociatedCoefficientSourceChangeIso_comp
    {k l r : ℕᵒᵖ} (f : k ⟶ l) (g : l ⟶ r) (i : Under r) :
    ((J).overMapPullback (ModuleCat.{0} R) ((covers).obj.map f)).map
        ((sourceChange g).hom.app i) ≫
      (sourceChange f).hom.app ((Under.map g).obj i) =
    ((J).overMapPullbackComp (ModuleCat.{0} R)
        ((covers).obj.map f) ((covers).obj.map g)).hom.app ((source r).obj i) ≫
      ((J).overMapPullbackCongr (ModuleCat.{0} R)
        ((covers).obj.map_comp f g).symm).hom.app ((source r).obj i) ≫
      (sourceChange (f ≫ g)).hom.app i :=
  sourceSliceChangeIso_comp J (ModuleCat.{0} R) (covers).obj f g system i

/-- Identity source change is the standard slice identity comparison,
with the identity law of the exact geometric cover diagram. -/
theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceChangeIso_id
    (k : ℕᵒᵖ) (i : Under k) :
    (restrictedChange (𝟙 k)).hom.app i =
      ((J).overMapPullbackCongr (ModuleCat.{0} R) ((covers).obj.map_id k)).hom.app
          ((restrictedSource k).obj i) ≫
        ((J).overMapPullbackId (ModuleCat.{0} R) ((covers).obj.obj k)).hom.app
          ((restrictedSource k).obj i) :=
  sourceSliceChangeIso_id J (ModuleCat.{0} R) (covers).obj k restrictedSystem i

/-- Successive source changes agree with the direct source change under
the actual slice-composition and geometric cover functor comparisons. -/
theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceChangeIso_comp
    {k l r : ℕᵒᵖ} (f : k ⟶ l) (g : l ⟶ r) (i : Under r) :
    ((J).overMapPullback (ModuleCat.{0} R) ((covers).obj.map f)).map
        ((restrictedChange g).hom.app i) ≫
      (restrictedChange f).hom.app ((Under.map g).obj i) =
    ((J).overMapPullbackComp (ModuleCat.{0} R)
        ((covers).obj.map f) ((covers).obj.map g)).hom.app ((restrictedSource r).obj i) ≫
      ((J).overMapPullbackCongr (ModuleCat.{0} R)
        ((covers).obj.map_comp f g).symm).hom.app ((restrictedSource r).obj i) ≫
      (restrictedChange (f ≫ g)).hom.app i :=
  sourceSliceChangeIso_comp J (ModuleCat.{0} R) (covers).obj f g restrictedSystem i

/-- Identity source change is the standard slice identity comparison,
with the identity law of the exact geometric cover diagram. -/
theorem cmHarrisGeometricConstantCoefficientSourceChangeIso_id
    (k : ℕᵒᵖ) (i : Under k) :
    (constantChange (𝟙 k)).hom.app i =
      ((J).overMapPullbackCongr (ModuleCat.{0} R) ((covers).obj.map_id k)).hom.app
          ((constantSource k).obj i) ≫
        ((J).overMapPullbackId (ModuleCat.{0} R) ((covers).obj.obj k)).hom.app
          ((constantSource k).obj i) :=
  sourceSliceChangeIso_id J (ModuleCat.{0} R) (covers).obj k ((coefficients).obj ⋙ constantSheaf J (ModuleCat.{0} R)) i

/-- Successive source changes agree with the direct source change under
the actual slice-composition and geometric cover functor comparisons. -/
theorem cmHarrisGeometricConstantCoefficientSourceChangeIso_comp
    {k l r : ℕᵒᵖ} (f : k ⟶ l) (g : l ⟶ r) (i : Under r) :
    ((J).overMapPullback (ModuleCat.{0} R) ((covers).obj.map f)).map
        ((constantChange g).hom.app i) ≫
      (constantChange f).hom.app ((Under.map g).obj i) =
    ((J).overMapPullbackComp (ModuleCat.{0} R)
        ((covers).obj.map f) ((covers).obj.map g)).hom.app ((constantSource r).obj i) ≫
      ((J).overMapPullbackCongr (ModuleCat.{0} R)
        ((covers).obj.map_comp f g).symm).hom.app ((constantSource r).obj i) ≫
      (constantChange (f ≫ g)).hom.app i :=
  sourceSliceChangeIso_comp J (ModuleCat.{0} R) (covers).obj f g ((coefficients).obj ⋙ constantSheaf J (ModuleCat.{0} R)) i

/-- Localize the published whole-system scalar comparison on one exact source. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso (k : ℕᵒᵖ) :
    (restrictedSource k) ≅ (source k) :=
  Functor.isoWhiskerLeft (Under.forget k)
    (Functor.isoWhiskerRight systemComparison (localize k))

local notation "sourceComparison" k => cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k

/-- Each component is the same global scalar comparison restricted to this source. -/
@[simp] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    (sourceComparison k).hom.app i =
      (localize k).map ((systemComparison).hom.app i.right) := rfl

@[simp] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_inv_app
    (k : ℕᵒᵖ) (i : Under k) :
    (sourceComparison k).inv.app i =
      (localize k).map ((systemComparison).inv.app i.right) := rfl

/-- The source scalar comparison preserves every original transported transition. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    (localize k).map ((restrictedSystem).map f.right) ≫
        (sourceComparison k).hom.app j =
      (sourceComparison k).hom.app i ≫ (localize k).map ((system).map f.right) :=
  (sourceComparison k).hom.naturality f

/-- The published restricted evaluation factors through the same source scalar iso. -/
theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_trivialization (k : ℕᵒᵖ) :
    (sourceComparison k) ≪≫ (sourceTrivialization k) = (restrictedTrivialization k) := rfl

/-- Changing source commutes with the complete scalar comparison. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_sourceChange
    {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (restrictSource f).map (sourceComparison l).hom ≫ (sourceChange f).hom =
      (restrictedChange f).hom ≫ (reindexSource f).map (sourceComparison k).hom :=
  (sourceSliceChangeFunctorIso J (ModuleCat.{0} R) (covers).obj f).hom.naturality
    (systemComparison).hom

/-- Actual integral invariant evaluation commutes with exact geometric source change. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceTrivialization_sourceChange
    {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (restrictSource f).map (sourceTrivialization l).hom ≫ (constantChange f).hom =
      (sourceChange f).hom ≫ (reindexSource f).map (sourceTrivialization k).hom :=
  etaleAssociatedSourceTrivialization_sourceChange X covers coverProperty f coefficients

/-- The same square holds for scalar-restricted quotient evaluation, with every
coefficient reduction retained in the diagram. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization_sourceChange
    {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (restrictSource f).map (restrictedTrivialization l).hom ≫ (constantChange f).hom =
      (restrictedChange f).hom ≫
        (reindexSource f).map (restrictedTrivialization k).hom := by
  change (restrictSource f).map
      ((sourceComparison l).hom ≫ (sourceTrivialization l).hom) ≫ _ =
    _ ≫ (reindexSource f).map
      ((sourceComparison k).hom ≫ (sourceTrivialization k).hom)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc,
    cmHarrisGeometricAssociatedCoefficientSourceTrivialization_sourceChange D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor
      q U ρ p m hm existence geometry hRigid f,
    ← Category.assoc,
    cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_sourceChange D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor
      q U ρ p m hm existence geometry hRigid f,
    Category.assoc]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
