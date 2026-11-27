import Langlands.Shimura.PEL.HarrisTaylorCMUniversalClass
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathProof

/-! # Polarized rational transport of the universal CM families -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
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

local notation "component" => componentCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "componentHom" => componentCMBaseHomTo D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "point" => cmUniversalComponentPoint D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "representative" => cmUniversalRepresentative D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  {U V : SmallCMLevel D} (b : U ⟶ V)
  (c : _root_.ConnectedComponents (R U).base.obj.left)

local notation "d" => componentMap ((baseTower R).map b).hom.left c
local notation "source" => component (R U).base c
local notation "target" => component (R V).base d
local notation "f" => componentHom ((baseTower R).map b) c d rfl
local notation "s" => point (R U) c
local notation "t" => point (R V) d

/-- A finite étale fibre-functor path over the image component. -/
abbrev cmUniversalLevelPath :=
  fiberFunctor (t).hom (t).finiteFibers ≅
    fiberFunctor ((s).comp (f).hom.left).hom ((s).comp (f).hom.left).finiteFibers

local notation "Path" => cmUniversalLevelPath D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor R b c

/-- A path from the target representative's point to the image of the source point. -/
def cmUniversalLevelPathChoice : Path :=
  Classical.choice (geometricPathExists (t).hom ((s).comp (f).hom.left).hom
    (t).finiteFibers ((s).comp (f).hom.left).finiteFibers)

/-- The source representative with its orbit pushed along the level arrow. -/
def cmUniversalLevelSource :=
  HarrisNumericalWeilLevel.mapRepresentative D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    (s).hom (s).finiteFibers htor (source).property.torsionUnits ((ObjectProperty.ι _).map b)
    (representative (R U) c)

/-- The target representative with its transported orbit, pulled back to the source component. -/
def cmUniversalLevelTarget (path : Path) :=
  levelDataBaseChange D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability (f).hom.left
    compatibility h (s).hom (s).finiteFibers ((s).comp (f).hom.left).finiteFibers htor
    (target).property.torsionUnits (source).property.torsionUnits
    (unpointedPullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality f) V.obj
    (HarrisTaylorLieWeilLevel.pointMapRepresentative D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h htor (target).property.torsionUnits path V.obj (representative (R V) d))

local notation "Sdata" => cmUniversalLevelSource D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor R b c
local notation "Tdata" => cmUniversalLevelTarget D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor R b c

/-- An actual rational isomorphism over the source component, scaling the polarization
by its rational multiplier and carrying the pushed source orbit to the pulled-back orbit. -/
structure CMUniversalLevelTransport (path : Path) where
  multiplier : ℚˣ
  iso : letI := auxiliaryStarRing D C; (Sdata).1.actionObj ≅ (Tdata path).1.actionObj
  scales : letI := auxiliaryStarRing D C
    PolarizedWeilLevel.Multiple preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (source).property.pairAdditivity (Sdata).1 (Tdata path).1 multiplier iso
  orbit_eq : letI := auxiliaryStarRing D C
    PolarizedWeilLevel.levelIso preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) (s).hom (s).finiteFibers htor (source).property.torsionUnits
    (source).property.pairAdditivity (Sdata).1 (Tdata path).1
    ((hodgeLevelFunctor D C).obj V.obj) multiplier iso scales (Sdata).2 = (Tdata path).2

local notation "Transport" => CMUniversalLevelTransport D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor R b c

/-- The Yoneda transition of universal classes gives a polarized rational isomorphism
of the representatives for every choice of the target fibre-functor path. -/
theorem cmUniversalLevelTransport_nonempty (path : Path) : Nonempty (Transport path) := by
  let := auxiliaryStarRing D C
  obtain ⟨hx, hn, heq⟩ := cmUniversalRepresentative_transition D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R b c d rfl s path
  have hSource := cmUniversalComponentRepresentative_good D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor (R U) c s
  have hNumerical := cmUniversalComponentRepresentative_numerical D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor (R U) c s
  obtain ⟨a, e, hm, he⟩ := (HarrisNumericalWeilLevel.classOf_eq_iff D C
    (isCMSection_harrisCMSection E (algebraMap L F) τ₀) preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C (source).obj.hom) compatibility h
    (s).hom (s).finiteFibers htor (source).property.torsionUnits (source).property.pairAdditivity
    L (source).obj.hom Sdata (Tdata path) hSource hx hNumerical hn).mp heq.symm
  exact ⟨⟨a, e, hm, he⟩⟩

/-- Choose a compatible rational isomorphism of the actual representatives. -/
def cmUniversalLevelTransport (path : Path) : Transport path :=
  Classical.choice (cmUniversalLevelTransport_nonempty D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R b c path)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
