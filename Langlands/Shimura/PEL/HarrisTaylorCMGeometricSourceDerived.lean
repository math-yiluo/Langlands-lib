import Langlands.Shimura.PEL.HarrisTaylorCMGeometricSourceChange
import Langlands.Shimura.Coefficients.VaryingCoverDerivedSourceChange

/-! # Derived source diagrams for exact geometric CM coefficients -/

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

attribute [local instance] etaleAssociatedSourceSystemFunctorPreservesFiniteLimits
  etaleAssociatedSourceSystemFunctorPreservesFiniteColimits

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

/-- Exact derived association of complete coefficient diagrams on one exact
geometric full-kernel CM cover. -/
def cmHarrisGeometricAssociatedCoefficientSourceDerivedFunctor :
    DerivedCategory.{wC} coefficientCategory ⥤ DerivedCategory.{wS} (sourceCategory k) :=
  etaleAssociatedSourceDerivedFunctor X covers coverProperty k

/-- The unchanged coefficient diagram made constant on the same derived source. -/
def cmHarrisGeometricConstantCoefficientSourceDerivedFunctor :
    DerivedCategory.{wC} coefficientCategory ⥤ DerivedCategory.{wS} (sourceCategory k) :=
  etaleConstantSourceDerivedFunctor X covers k

local notation "associatedDerived" => cmHarrisGeometricAssociatedCoefficientSourceDerivedFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k
local notation "constantDerived" => cmHarrisGeometricConstantCoefficientSourceDerivedFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k

instance : (associatedDerived).CommShift ℤ := by
  dsimp only [cmHarrisGeometricAssociatedCoefficientSourceDerivedFunctor]
  infer_instance

instance : (associatedDerived).IsTriangulated := by
  dsimp only [cmHarrisGeometricAssociatedCoefficientSourceDerivedFunctor]
  infer_instance

instance : (constantDerived).CommShift ℤ := by
  dsimp only [cmHarrisGeometricConstantCoefficientSourceDerivedFunctor]
  infer_instance

instance : (constantDerived).IsTriangulated := by
  dsimp only [cmHarrisGeometricConstantCoefficientSourceDerivedFunctor]
  infer_instance

/-- The proved invariant evaluation descends on the whole actual derived
coefficient category, with every exponent reduction retained. -/
def cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization :
    associatedDerived ≅ constantDerived :=
  etaleAssociatedSourceDerivedTrivialization X covers coverProperty k

local notation "derivedTrivialization" =>
  cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    q U ρ p m hm existence geometry hRigid k

instance : NatTrans.CommShift (derivedTrivialization).hom ℤ := by
  dsimp only [cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization]
  infer_instance

/-- The derived evaluation at a cochain representative is the localization of
the actual termwise invariant-evaluation transformation. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_hom_app_Q_obj
    (T : CochainComplex coefficientCategory ℤ) :
    (derivedTrivialization).hom.app (DerivedCategory.Q.obj T) =
      (associatedSourceFunctor k).mapDerivedCategoryFactors.hom.app T ≫
        DerivedCategory.Q.map
          (((etaleAssociatedSourceTrivializationFunctor X covers coverProperty k).hom.mapHomologicalComplex
            (ComplexShape.up ℤ)).app T) ≫
        (constantSourceFunctor k).mapDerivedCategoryFactors.inv.app T :=
  etaleAssociatedSourceDerivedTrivialization_hom_app_Q_obj X covers coverProperty k T

/-- The actual full Harris coefficient diagram placed in degree d, associated
on the derived category of its entire reachable source diagram. -/
def cmHarrisGeometricAssociatedCoefficientSourceDerivedObject (d : ℤ) :
    DerivedCategory.{wS} (sourceCategory k) :=
  (associatedDerived).obj (derivedCoefficient d)

/-- The original full-lattice diagram in degree d on the same constant source. -/
def cmHarrisGeometricConstantCoefficientSourceDerivedObject (d : ℤ) :
    DerivedCategory.{wS} (sourceCategory k) :=
  (constantDerived).obj (derivedCoefficient d)

local notation "associatedObject" d => cmHarrisGeometricAssociatedCoefficientSourceDerivedObject D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k d
local notation "constantObject" d => cmHarrisGeometricConstantCoefficientSourceDerivedObject D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k d

/-- Recover the published ordinary associated source diagram in every degree. -/
def cmHarrisGeometricAssociatedCoefficientSourceDerivedObjectIso (d : ℤ) :
    (associatedObject d) ≅ (DerivedCategory.singleFunctor (sourceCategory k) d).obj (source k) :=
  ((associatedSourceFunctor k).mapDerivedCategorySingleFunctor d).app coefficients

/-- Recover the unchanged ordinary constant reduction diagram in every degree. -/
def cmHarrisGeometricConstantCoefficientSourceDerivedObjectIso (d : ℤ) :
    (constantObject d) ≅ (DerivedCategory.singleFunctor (sourceCategory k) d).obj (constantSource k) :=
  ((constantSourceFunctor k).mapDerivedCategorySingleFunctor d).app coefficients

local notation "associatedObjectIso" d => cmHarrisGeometricAssociatedCoefficientSourceDerivedObjectIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k d
local notation "constantObjectIso" d => cmHarrisGeometricConstantCoefficientSourceDerivedObjectIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k d

/-- The derived map on the actual Harris coefficient object recovers exactly
the original invariant evaluation under the canonical single-degree comparisons. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_hom_app_single
    (d : ℤ) :
    (derivedTrivialization).hom.app (derivedCoefficient d) =
      (associatedObjectIso d).hom ≫
        (DerivedCategory.singleFunctor (sourceCategory k) d).map (sourceTrivialization k).hom ≫
        (constantObjectIso d).inv :=
  etaleAssociatedSourceDerivedTrivialization_hom_app_single X covers coverProperty k coefficients d

end FixedSource

section SourceChange

variable {k l : ℕᵒᵖ}
variable [HasDerivedCategory.{wK}
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
variable [HasDerivedCategory.{wL}
  (Under l ⥤ Sheaf
    ((Scheme.smallEtaleTopology
      (Functor.obj (cmGeometricSchemeTower D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q) U)).over
      ((cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid).obj.obj l))
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]
variable [HasDerivedCategory.{wM}
  (Under l ⥤ Sheaf
    ((Scheme.smallEtaleTopology
      (Functor.obj (cmGeometricSchemeTower D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q) U)).over
      ((cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid).obj.obj k))
    (ModuleCat.{0} (HarrisCoefficientIntegers K p)))]

local notation "derivedAssociatedAt" i => cmHarrisGeometricAssociatedCoefficientSourceDerivedFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid i
local notation "derivedConstantAt" i => cmHarrisGeometricConstantCoefficientSourceDerivedFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid i
local notation "derivedEvaluationAt" i => cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid i
local notation "ordinaryRestriction" f => cmHarrisGeometricCoefficientSourceRestriction D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f
local notation "ordinaryReindex" f => cmHarrisGeometricCoefficientSourceReindex D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f
local notation "ordinaryAssociatedChange" f => cmHarrisGeometricAssociatedCoefficientSourceChangeIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f
local notation "ordinaryConstantChange" f => cmHarrisGeometricConstantCoefficientSourceChangeIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f

instance cmHarrisGeometricCoefficientSourceRestriction_additive (f : k ⟶ l) :
    (ordinaryRestriction f).Additive := by
  dsimp only [cmHarrisGeometricCoefficientSourceRestriction]
  infer_instance

instance cmHarrisGeometricCoefficientSourceRestriction_preservesFiniteLimits (f : k ⟶ l) :
    PreservesFiniteLimits (ordinaryRestriction f) := by
  dsimp only [cmHarrisGeometricCoefficientSourceRestriction]
  infer_instance

instance cmHarrisGeometricCoefficientSourceRestriction_preservesFiniteColimits (f : k ⟶ l) :
    PreservesFiniteColimits (ordinaryRestriction f) := by
  dsimp only [cmHarrisGeometricCoefficientSourceRestriction]
  infer_instance

instance cmHarrisGeometricCoefficientSourceReindex_additive (f : k ⟶ l) :
    (ordinaryReindex f).Additive := by
  dsimp only [cmHarrisGeometricCoefficientSourceReindex]
  infer_instance

instance cmHarrisGeometricCoefficientSourceReindex_preservesFiniteLimits (f : k ⟶ l) :
    PreservesFiniteLimits (ordinaryReindex f) := by
  dsimp only [cmHarrisGeometricCoefficientSourceReindex]
  infer_instance

instance cmHarrisGeometricCoefficientSourceReindex_preservesFiniteColimits (f : k ⟶ l) :
    PreservesFiniteColimits (ordinaryReindex f) := by
  dsimp only [cmHarrisGeometricCoefficientSourceReindex]
  infer_instance

/-- Restrict the entire source diagram along the exact geometric CM cover map
on actual unbounded derived categories. -/
def cmHarrisGeometricCoefficientSourceRestrictionDerivedFunctor (f : k ⟶ l) :
    DerivedCategory.{wL} (sourceCategory l) ⥤ DerivedCategory.{wM} (mixedCategory k, l) :=
  etaleSourceRestrictionDerivedFunctor (R := Rcoeff) X covers f

/-- Reindex the entire derived diagram by composition of outgoing cover arrows. -/
def cmHarrisGeometricCoefficientSourceReindexDerivedFunctor (f : k ⟶ l) :
    DerivedCategory.{wK} (sourceCategory k) ⥤ DerivedCategory.{wM} (mixedCategory k, l) :=
  etaleSourceReindexDerivedFunctor (R := Rcoeff) X covers f

local notation "derivedRestriction" f => cmHarrisGeometricCoefficientSourceRestrictionDerivedFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f
local notation "derivedReindex" f => cmHarrisGeometricCoefficientSourceReindexDerivedFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f

instance (f : k ⟶ l) : (derivedRestriction f).CommShift ℤ := by
  dsimp only [cmHarrisGeometricCoefficientSourceRestrictionDerivedFunctor]
  infer_instance

instance (f : k ⟶ l) : (derivedRestriction f).IsTriangulated := by
  dsimp only [cmHarrisGeometricCoefficientSourceRestrictionDerivedFunctor]
  infer_instance

instance (f : k ⟶ l) : (derivedReindex f).CommShift ℤ := by
  dsimp only [cmHarrisGeometricCoefficientSourceReindexDerivedFunctor]
  infer_instance

instance (f : k ⟶ l) : (derivedReindex f).IsTriangulated := by
  dsimp only [cmHarrisGeometricCoefficientSourceReindexDerivedFunctor]
  infer_instance

/-- Descend the actual associated source-change comparison through localization
of the complete equivariant coefficient diagram category. -/
def cmHarrisGeometricAssociatedCoefficientSourceDerivedChangeIso (f : k ⟶ l) :
    (derivedAssociatedAt l) ⋙ (derivedRestriction f) ≅
      (derivedAssociatedAt k) ⋙ (derivedReindex f) :=
  etaleAssociatedSourceDerivedChangeIso X covers coverProperty f

/-- The same derived source comparison for the unchanged constant coefficient diagram. -/
def cmHarrisGeometricConstantCoefficientSourceDerivedChangeIso (f : k ⟶ l) :
    (derivedConstantAt l) ⋙ (derivedRestriction f) ≅
      (derivedConstantAt k) ⋙ (derivedReindex f) :=
  etaleConstantSourceDerivedChangeIso X covers f

local notation "derivedAssociatedChange" f => cmHarrisGeometricAssociatedCoefficientSourceDerivedChangeIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f

instance (f : k ⟶ l) : NatTrans.CommShift (derivedAssociatedChange f).hom ℤ := by
  dsimp only [cmHarrisGeometricAssociatedCoefficientSourceDerivedChangeIso]
  infer_instance

local notation "derivedConstantChange" f => cmHarrisGeometricConstantCoefficientSourceDerivedChangeIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid f

instance (f : k ⟶ l) : NatTrans.CommShift (derivedConstantChange f).hom ℤ := by
  dsimp only [cmHarrisGeometricConstantCoefficientSourceDerivedChangeIso]
  infer_instance

/-- On a cochain representative, source change is the localization of the
actual termwise comparison through the canonical exact-functor factors. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceDerivedChangeIso_hom_app_Q_obj
    (f : k ⟶ l) (T : CochainComplex coefficientCategory ℤ) :
    (derivedAssociatedChange f).hom.app (DerivedCategory.Q.obj T) =
      (derivedRestriction f).map
          ((associatedSourceFunctor l).mapDerivedCategoryFactors.hom.app T) ≫
        (ordinaryRestriction f).mapDerivedCategoryFactors.hom.app
          (((associatedSourceFunctor l).mapHomologicalComplex _).obj T) ≫
        DerivedCategory.Q.map
          (((etaleAssociatedSourceChangeFunctorIso X covers coverProperty f).hom.mapHomologicalComplex
            (ComplexShape.up ℤ)).app T) ≫
        (ordinaryReindex f).mapDerivedCategoryFactors.inv.app
          (((associatedSourceFunctor k).mapHomologicalComplex _).obj T) ≫
        (derivedReindex f).map
          ((associatedSourceFunctor k).mapDerivedCategoryFactors.inv.app T) :=
  etaleAssociatedSourceDerivedChangeIso_hom_app_Q_obj X covers coverProperty f T

/-- On the actual Harris coefficient diagram in any single degree, recover
exactly the published ordinary source change, including its reduction maps. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceDerivedChangeIso_hom_app_single
    (f : k ⟶ l) (d : ℤ) :
    (derivedAssociatedChange f).hom.app (derivedCoefficient d) =
      (derivedRestriction f).map
          (((associatedSourceFunctor l).mapDerivedCategorySingleFunctor d).hom.app coefficients) ≫
        ((ordinaryRestriction f).mapDerivedCategorySingleFunctor d).hom.app (source l) ≫
        (DerivedCategory.singleFunctor (mixedCategory k, l) d).map
          (ordinaryAssociatedChange f).hom ≫
        ((ordinaryReindex f).mapDerivedCategorySingleFunctor d).inv.app (source k) ≫
        (derivedReindex f).map
          (((associatedSourceFunctor k).mapDerivedCategorySingleFunctor d).inv.app coefficients) :=
  etaleAssociatedSourceDerivedChangeIso_hom_app_single X covers coverProperty f coefficients d

/-- On a cochain representative, source change is the localization of the
actual termwise comparison through the canonical exact-functor factors. -/
@[reassoc] theorem cmHarrisGeometricConstantCoefficientSourceDerivedChangeIso_hom_app_Q_obj
    (f : k ⟶ l) (T : CochainComplex coefficientCategory ℤ) :
    (derivedConstantChange f).hom.app (DerivedCategory.Q.obj T) =
      (derivedRestriction f).map
          ((constantSourceFunctor l).mapDerivedCategoryFactors.hom.app T) ≫
        (ordinaryRestriction f).mapDerivedCategoryFactors.hom.app
          (((constantSourceFunctor l).mapHomologicalComplex _).obj T) ≫
        DerivedCategory.Q.map
          (((etaleConstantSourceChangeFunctorIso X covers f).hom.mapHomologicalComplex
            (ComplexShape.up ℤ)).app T) ≫
        (ordinaryReindex f).mapDerivedCategoryFactors.inv.app
          (((constantSourceFunctor k).mapHomologicalComplex _).obj T) ≫
        (derivedReindex f).map
          ((constantSourceFunctor k).mapDerivedCategoryFactors.inv.app T) :=
  etaleConstantSourceDerivedChangeIso_hom_app_Q_obj X covers f T

/-- On the actual Harris coefficient diagram in any single degree, recover
exactly the published ordinary source change, including its reduction maps. -/
@[reassoc] theorem cmHarrisGeometricConstantCoefficientSourceDerivedChangeIso_hom_app_single
    (f : k ⟶ l) (d : ℤ) :
    (derivedConstantChange f).hom.app (derivedCoefficient d) =
      (derivedRestriction f).map
          (((constantSourceFunctor l).mapDerivedCategorySingleFunctor d).hom.app coefficients) ≫
        ((ordinaryRestriction f).mapDerivedCategorySingleFunctor d).hom.app (constantSource l) ≫
        (DerivedCategory.singleFunctor (mixedCategory k, l) d).map
          (ordinaryConstantChange f).hom ≫
        ((ordinaryReindex f).mapDerivedCategorySingleFunctor d).inv.app (constantSource k) ≫
        (derivedReindex f).map
          (((constantSourceFunctor k).mapDerivedCategorySingleFunctor d).inv.app coefficients) :=
  etaleConstantSourceDerivedChangeIso_hom_app_single X covers f coefficients d

/-- Actual invariant evaluation commutes with exact geometric source change
as an equality of natural transformations on the whole derived category. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_sourceChange
    (f : k ⟶ l) :
    Functor.whiskerRight (derivedEvaluationAt l).hom (derivedRestriction f) ≫
        (derivedConstantChange f).hom =
      (derivedAssociatedChange f).hom ≫
        Functor.whiskerRight (derivedEvaluationAt k).hom (derivedReindex f) :=
  etaleAssociatedSourceDerivedTrivialization_sourceChange X covers coverProperty f

/-- The same derived square evaluated at any derived coefficient object. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_sourceChange_app
    (f : k ⟶ l) (T : DerivedCategory.{wC} coefficientCategory) :
    (derivedRestriction f).map ((derivedEvaluationAt l).hom.app T) ≫
        (derivedConstantChange f).hom.app T =
      (derivedAssociatedChange f).hom.app T ≫
        (derivedReindex f).map ((derivedEvaluationAt k).hom.app T) :=
  etaleAssociatedSourceDerivedTrivialization_sourceChange_app X covers coverProperty f T

end SourceChange

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
