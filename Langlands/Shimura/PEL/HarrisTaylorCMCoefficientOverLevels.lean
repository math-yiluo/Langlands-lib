import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedSystem
import Langlands.Shimura.Coefficients.EtaleInverseImageVaryingSystem
import Langlands.Geometry.EtaleCanonicalCoefficientDiagram

/-! # Nonconstant Harris coefficients over actual CM coarse-level transporters -/

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
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Geometry.EtaleInverseImage

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
local notation "baseSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "baseInclusion" => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

/-- The existing geometric CM schemes indexed by specified small-level arrows to U. -/
def cmHarrisGeometricOverLevelSchemes : Over U ⥤ Scheme :=
  Over.forget U ⋙ geometricSchemes q

local notation "overSchemes" => cmHarrisGeometricOverLevelSchemes D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U

/-- Every projection is the original scheme map of the specified transporter. -/
def cmHarrisGeometricOverLevelProjection :
    overSchemes ⟶ (Functor.const (Over U)).obj Xbar where
  app V := (geometricSchemes q).map V.hom
  naturality V Z a := by
    change (geometricSchemes q).map a.left ≫ (geometricSchemes q).map Z.hom =
      (geometricSchemes q).map V.hom ≫ 𝟙 Xbar
    rw [Category.comp_id, ← (geometricSchemes q).map_comp, Over.w a]

local notation "projection" => cmHarrisGeometricOverLevelProjection D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U

/-- The actual opposite scheme cone, used by arbitrary-morphism coefficient descent. -/
def cmHarrisGeometricOverLevelBaseCone :
    (Functor.const (Over U)ᵒᵖ).obj (op Xbar) ⟶ (overSchemes).op where
  app V := ((projection).app V.unop).op
  naturality V Z a := by
    apply Quiver.Hom.unop_inj
    change (projection).app Z.unop ≫ 𝟙 Xbar =
      (overSchemes).map a.unop ≫ (projection).app V.unop
    exact ((projection).naturality a.unop).symm

local notation "baseCone" => cmHarrisGeometricOverLevelBaseCone D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U

/-- The entire nonconstant full Harris system on every actual transporter to U.
Both exponent and coarse-level compatibilities are constructed by inverse-image coherence. -/
def cmHarrisGeometricCoefficientOverLevels :
    ℕᵒᵖ ⥤ EtaleGeometricDiagram.CoefficientDiagram R (overSchemes).op :=
  baseSystem ⋙ EtaleGeometricDiagram.canonicalCoefficientsFunctor R baseCone

local notation "system" => cmHarrisGeometricCoefficientOverLevels D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The coefficient is the actual inverse image of the nonconstant Harris sheaf. -/
@[simp] theorem cmHarrisGeometricCoefficientOverLevels_obj_obj
    (k : ℕᵒᵖ) (V : Over U) :
    ((system).obj k).obj (op V) =
      (inverseImage ((geometricSchemes q).map V.hom) R).obj ((baseSystem).obj k) := rfl

/-- Exponent transitions retain exactly the original Harris reduction morphism. -/
@[simp] theorem cmHarrisGeometricCoefficientOverLevels_map_app
    {i j : ℕᵒᵖ} (f : i ⟶ j) (V : Over U) :
    ((system).map f).app (op V) =
      (inverseImage ((geometricSchemes q).map V.hom) R).map ((baseSystem).map f) := rfl

/-- Coarse-level transitions use the actual commuting transporter triangle. -/
theorem cmHarrisGeometricCoefficientOverLevels_obj_map
    (k : ℕᵒᵖ) {V Z : Over U} (a : V ⟶ Z) :
    ((system).obj k).map a.op =
      (projectionInverseImageIso R
        ((geometricSchemes q).map Z.hom) ((geometricSchemes q).map V.hom)
        ((geometricSchemes q).map a.left)
        (((geometricSchemes q).map_comp a.left Z.hom).symm.trans
          (congrArg (geometricSchemes q).map (Over.w a)))).hom.app ((baseSystem).obj k) := rfl

/-- Every coarse transition is an isomorphism of the actual inverse-image sheaves. -/
instance cmHarrisGeometricCoefficientOverLevels_obj_map_isIso
    (k : ℕᵒᵖ) {V Z : Over U} (a : V ⟶ Z) :
    IsIso (((system).obj k).map a.op) :=
  EtaleGeometricDiagram.canonicalCoefficients_map_isIso R baseCone ((baseSystem).obj k) a.op

/-- The two constructed index directions commute as sheaf morphisms. -/
@[reassoc] theorem cmHarrisGeometricCoefficientOverLevels_reduction_transport
    {i j : ℕᵒᵖ} (f : i ⟶ j) {V Z : Over U} (a : V ⟶ Z) :
    ((system).obj i).map a.op ≫ ((system).map f).app (op V) =
      (inverseImage ((geometricSchemes q).map a.left) R).map
          (((system).map f).app (op Z)) ≫ ((system).obj j).map a.op :=
  ((system).map f).comm a.op

/-- Evaluation at a specified transporter gives the whole inverse-image system. -/
def cmHarrisGeometricCoefficientOverLevelsEvaluationIso (V : Over U) :
    system ⋙ EtaleGeometricDiagram.CoefficientDiagram.evaluation (op V) ≅
      baseSystem ⋙ inverseImage ((geometricSchemes q).map V.hom) R := Iso.refl _

/-- At the identity transporter, the original entire nonconstant system is recovered. -/
def cmHarrisGeometricCoefficientOverLevelsIdentityIso :
    system ⋙ EtaleGeometricDiagram.CoefficientDiagram.evaluation (op (Over.mk (𝟙 U))) ≅
      baseSystem :=
  Functor.isoWhiskerLeft baseSystem
    (inverseImageCongr R ((geometricSchemes q).map_id U) ≪≫ inverseImageId R Xbar) ≪≫
      Functor.rightUnitor baseSystem

/-- Pull back the existing exact geometric coefficient covers along the specified
original transporter map, without selecting new lattice or level data. -/
def cmHarrisGeometricOverLevelCoefficientCovers (V : Over U) :
    EquivariantDiagram groups ((geometricSchemes q).obj V.left).Etale :=
  (etaleTorsorDiagramPullback ((geometricSchemes q).map V.hom) groups).obj covers

local notation "pulledCovers" V => cmHarrisGeometricOverLevelCoefficientCovers D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid V

/-- The covers at every exponent remain finite geometric torsors. -/
theorem cmHarrisGeometricOverLevelCoefficientCovers_isFiniteGeometricTorsor
    (V : Over U) (k : ℕᵒᵖ) :
    IsFiniteGeometricTorsor ((geometricSchemes q).obj V.left) ((pulledCovers V).action k) :=
  etaleTorsorDiagramPullback_isFiniteGeometricTorsor
    ((geometricSchemes q).map V.hom) groups covers coverProperty k

local notation "pulledProperty" V => cmHarrisGeometricOverLevelCoefficientCovers_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid V

/-- The total scheme is the actual fiber product of the original coefficient cover
and the original coarse-level transporter map. -/
@[simp] theorem cmHarrisGeometricOverLevelCoefficientCovers_obj_left
    (V : Over U) (k : ℕᵒᵖ) :
    ((pulledCovers V).obj.obj k).left =
      Limits.pullback ((covers).obj.obj k).hom ((geometricSchemes q).map V.hom) := rfl

/-- The coarse projection is the second actual fiber-product projection. -/
@[simp] theorem cmHarrisGeometricOverLevelCoefficientCovers_obj_hom
    (V : Over U) (k : ℕᵒᵖ) :
    ((pulledCovers V).obj.obj k).hom =
      Limits.pullback.snd ((covers).obj.obj k).hom ((geometricSchemes q).map V.hom) := rfl

/-- On every specified coarse transporter, the complete inverse-image system is
association on those actual fiber-product covers with the unchanged coefficient diagram. -/
def cmHarrisGeometricCoefficientOverLevelsAssociatedIso (V : Over U) :
    system ⋙ EtaleGeometricDiagram.CoefficientDiagram.evaluation (op V) ≅
      etaleAssociatedVaryingSystem ((geometricSchemes q).obj V.left)
        (pulledCovers V) (pulledProperty V) coefficients :=
  (etaleAssociatedVaryingSystemInverseImage ((geometricSchemes q).map V.hom) R
    covers coverProperty).app coefficients

local notation "associatedIso" V => cmHarrisGeometricCoefficientOverLevelsAssociatedIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid V

/-- Its components are the canonical arbitrary-morphism torsor comparisons. -/
@[simp] theorem cmHarrisGeometricCoefficientOverLevelsAssociatedIso_hom_app
    (V : Over U) (k : ℕᵒᵖ) :
    (associatedIso V).hom.app k =
      (inverseImageConstantAssociatedIso ((geometricSchemes q).map V.hom) R
        ((covers).action k) (coverProperty k)).hom.app ((coefficients).action k) := rfl

/-- The cover interpretation preserves every exponent transition. -/
@[reassoc] theorem cmHarrisGeometricCoefficientOverLevelsAssociatedIso_transition
    (V : Over U) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((system).map f).app (op V) ≫ (associatedIso V).hom.app j =
      (associatedIso V).hom.app i ≫
        (etaleAssociatedVaryingSystem ((geometricSchemes q).obj V.left)
          (pulledCovers V) (pulledProperty V) coefficients).map f :=
  (associatedIso V).hom.naturality f

/-- The comparison is normalized on the original invariant inclusions, with
product-sheaf base change and the unchanged constant coefficient module. -/
@[reassoc] theorem cmHarrisGeometricCoefficientOverLevelsAssociatedIso_hom_inclusion
    (V : Over U) (k : ℕᵒᵖ) :
    (associatedIso V).hom.app k ≫
        etaleAssociatedInclusion ((geometricSchemes q).obj V.left)
          ((pulledCovers V).action k) ((coefficients).action k) =
      (inverseImage ((geometricSchemes q).map V.hom) R).map ((baseInclusion) k) ≫
        (inverseImageProductSheafIso ((geometricSchemes q).map V.hom) R
          ((covers).action k) (coverProperty k)
          ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj k))).hom ≫
        (productSheaf (Scheme.smallEtaleTopology ((geometricSchemes q).obj V.left))
          ((pulledCovers V).obj.obj k)).map
          ((inverseImageConstantIso ((geometricSchemes q).map V.hom) R).hom.app
            ((coefficients).obj.obj k)) :=
  inverseImageConstantAssociatedIso_hom_inclusion ((geometricSchemes q).map V.hom) R
    ((covers).action k) (coverProperty k) ((coefficients).action k)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
