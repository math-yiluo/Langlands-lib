import Langlands.Shimura.PEL.HarrisTaylorCMGeometricSourceDerived

/-! # Derived scalar comparisons for exact geometric CM source diagrams -/

noncomputable section

universe wC wS wK wL wM

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
open Langlands.Shimura.Coefficients Langlands.Sheaf Langlands.Cohomology

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
local notation "Rcoeff" => HarrisCoefficientIntegers K p
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
local notation "source" k => cmHarrisGeometricAssociatedCoefficientSourceSystem D C
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
local notation "groups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "coefficientCategory" => EquivariantDiagram groups (ModuleCat.{0} Rcoeff)
local notation "sourceCategory" k =>
  (Under k ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} Rcoeff))
local notation "mixedCategory" k "," l =>
  (Under l ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} Rcoeff))
local notation "associatedSourceFunctor" k =>
  etaleAssociatedSourceSystemFunctor X covers coverProperty k
local notation "constantSourceFunctor" k => etaleConstantSourceSystemFunctor X covers k
local notation "derivedCoefficient" d =>
  (DerivedCategory.singleFunctor coefficientCategory d).obj coefficients

local notation "restrictedSource" k => cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "sourceComparison" k => cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "restrictedTrivialization" k =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    q U ρ p m hm existence geometry hRigid k

variable [HasDerivedCategory.{wC}
  (EquivariantDiagram (cmHarrisCoefficientGroups D ρ p U m hm)
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]

section FixedSource

variable (k : ℕᵒᵖ) [HasDerivedCategory.{wS}
  (Under k ⥤ Sheaf
    ((Scheme.smallEtaleTopology
      (Functor.obj (cmGeometricSchemeTower D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q) U)).over
      ((cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid).obj.obj k))
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]

/-- The actual directly associated quotient coefficient source diagram,
after restriction to integral scalars, placed in degree d. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedObject (d : ℤ) :
    DerivedCategory.{wS} (sourceCategory k) :=
  (DerivedCategory.singleFunctor (sourceCategory k) d).obj (restrictedSource k)

local notation "restrictedObject" d => cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedObject
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d
local notation "associatedObject" d => cmHarrisGeometricAssociatedCoefficientSourceDerivedObject
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d
local notation "constantObject" d => cmHarrisGeometricConstantCoefficientSourceDerivedObject
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d
local notation "associatedObjectIso" d => cmHarrisGeometricAssociatedCoefficientSourceDerivedObjectIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d
local notation "constantObjectIso" d => cmHarrisGeometricConstantCoefficientSourceDerivedObjectIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d
local notation "derivedEvaluation" =>
  cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k

/-- The ordinary scalar comparison localized in one degree and identified
with the existing exact-derived associated coefficient object. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso (d : ℤ) :
    (restrictedObject d) ≅ (associatedObject d) :=
  (DerivedCategory.singleFunctor (sourceCategory k) d).mapIso (sourceComparison k) ≪≫
    (associatedObjectIso d).symm

local notation "derivedComparison" d => cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso
  D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d

/-- Recover the specific original scalar map, including the complete reachable
coefficient diagram, under the canonical associated-object comparison. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso_hom (d : ℤ) :
    (derivedComparison d).hom =
      (DerivedCategory.singleFunctor (sourceCategory k) d).map (sourceComparison k).hom ≫
        (associatedObjectIso d).inv := rfl

@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso_inv (d : ℤ) :
    (derivedComparison d).inv =
      (associatedObjectIso d).hom ≫
        (DerivedCategory.singleFunctor (sourceCategory k) d).map (sourceComparison k).inv := rfl

/-- Derived invariant evaluation of the actual scalar-restricted quotient
source system, through its proved scalar comparison. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization (d : ℤ) :
    (restrictedObject d) ≅ (constantObject d) :=
  (derivedComparison d) ≪≫ (derivedEvaluation).app (derivedCoefficient d)

local notation "restrictedDerivedEvaluation" d =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization
    D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d

/-- The whole isomorphism recovers the original restricted scalar evaluation,
with the canonical constant-object comparison in the target. -/
theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization_eq (d : ℤ) :
    (restrictedDerivedEvaluation d) =
      (DerivedCategory.singleFunctor (sourceCategory k) d).mapIso (restrictedTrivialization k) ≪≫
        (constantObjectIso d).symm := by
  apply Iso.ext
  dsimp only [cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization,
    cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  rw [cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_hom_app_single
    D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc]
  rfl

/-- The derived map is exactly the original quotient scalar evaluation in degree d. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization_hom
    (d : ℤ) :
    (restrictedDerivedEvaluation d).hom =
      (DerivedCategory.singleFunctor (sourceCategory k) d).map (restrictedTrivialization k).hom ≫
        (constantObjectIso d).inv := by
  rw [cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization_eq
    D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d]
  rfl

/-- The inverse has the same exact recovery, with its original inverse evaluation. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization_inv
    (d : ℤ) :
    (restrictedDerivedEvaluation d).inv =
      (constantObjectIso d).hom ≫
        (DerivedCategory.singleFunctor (sourceCategory k) d).map (restrictedTrivialization k).inv := by
  rw [cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization_eq
    D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k d]
  rfl

/-- Scalar comparison followed by the existing derived invariant evaluation
is the derived quotient scalar evaluation, as a complete isomorphism. -/
theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso_trivialization (d : ℤ) :
    (derivedComparison d) ≪≫ (derivedEvaluation).app (derivedCoefficient d) =
      (restrictedDerivedEvaluation d) := rfl

end FixedSource

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
