import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSchemes
import Langlands.Shimura.Coefficients.VaryingCoverInverse

/-! # Compatible full Harris coefficient sheaves on original CM scheme levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
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

local notation "schemes" => cmSchemeTower D C preservation composition
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
local notation "covers" => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "torsor" k => cmHarrisCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

/-- The inverse system of full Harris coefficient sheaves on the original CM scheme.
Its transitions invert the proved comparison for the actual original covers. -/
def cmHarrisCoefficientSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  etaleAssociatedVaryingSystem X covers coverProperty coefficients

local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Every component is associated to the original coefficient torsor with integral scalars. -/
@[simp] theorem cmHarrisCoefficientSystem_obj (k : ℕᵒᵖ) :
    (system).obj k =
      (etaleAssociatedFunctor X (torsor k.unop).val).obj ((coefficients).action k) := rfl

/-- The transition is coefficient reduction followed by the inverse original-cover comparison. -/
@[simp] theorem cmHarrisCoefficientSystem_map {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f =
      (etaleAssociatedReduction X covers f).app coefficients ≫
        (etaleAssociatedComparisonIso X covers coverProperty f).inv.app coefficients := rfl

/-- The exact comparison leg for the original CM covers is invertible. -/
theorem cmHarrisCoefficientSystem_comparison_isIso
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    IsIso ((etaleAssociatedComparison X covers f).app coefficients) :=
  etaleAssociatedComparison_app_isIso X covers coverProperty f coefficients

/-- Composing a transition with that exact comparison recovers coefficient reduction. -/
@[reassoc] theorem cmHarrisCoefficientSystem_map_comparison
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f ≫ (etaleAssociatedComparison X covers f).app coefficients =
      (etaleAssociatedReduction X covers f).app coefficients :=
  etaleAssociatedTransition_comparison X covers coverProperty f coefficients

/-- The canonical invariant-section inclusion at every actual coefficient level. -/
def cmHarrisCoefficientSystemInclusion (k : ℕᵒᵖ) :
    (system).obj k ⟶
      (productSheaf J ((covers).obj.obj k)).obj
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) :=
  etaleAssociatedInclusion X ((covers).action k) ((coefficients).action k)

local notation "inc" => cmHarrisCoefficientSystemInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The inclusions are monomorphisms of actual small-etale sheaves. -/
instance cmHarrisCoefficientSystemInclusion_mono (k : ℕᵒᵖ) : Mono ((inc) k) :=
  etaleAssociatedInclusion_mono X ((covers).action k) ((coefficients).action k)

set_option quotPrecheck false in
local notation "constantAction" k =>
  Functor.obj (Functor.mapAction (constantSheaf J (ModuleCat.{0} R))
    ((cmHarrisCoefficientGroups D ρ p U m hm).obj k)) ((coefficients).action k)

/-- Sections retain the original diagonal coefficient and inverse-deck invariance. -/
@[reassoc] theorem cmHarrisCoefficientSystemInclusion_invariant
    (k : ℕᵒᵖ) (g : (cmHarrisCoefficientGroups D ρ p U m hm).obj k) :
    (inc) k ≫ (diagonal J ((covers).action k) (constantAction k)).ρ g = (inc) k :=
  inclusion_invariant J ((covers).action k) (constantAction k) g

/-- On actual cover sections, reduction commutes with original CM forgetting pullback. -/
@[reassoc] theorem cmHarrisCoefficientSystem_map_inclusion
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f ≫ (inc) j ≫
        coverPullback J ((covers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj j)) =
      (inc) i ≫ (productSheaf J ((covers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((coefficients).obj.map f)) :=
  etaleAssociatedTransition_inclusion X covers coverProperty f coefficients

/-- The section equation determines each transition uniquely. -/
theorem cmHarrisCoefficientSystem_map_unique
    {i j : ℕᵒᵖ} (f : i ⟶ j)
    (a : (system).obj i ⟶ (system).obj j)
    (ha : a ≫ (inc) j ≫
        coverPullback J ((covers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj j)) =
      (inc) i ≫ (productSheaf J ((covers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((coefficients).obj.map f))) :
    a = (system).map f := by
  apply etaleAssociatedTransition_hom_ext X covers coverProperty f coefficients
  exact ha.trans (cmHarrisCoefficientSystem_map_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f).symm

/-- Every component trivializes on its original full coefficient cover. -/
def cmHarrisCoefficientSystemTrivialization (k : ℕᵒᵖ) :
    ((J).overPullback (ModuleCat.{0} R) ((covers).obj.obj k)).obj ((system).obj k) ≅
      ((J).overPullback (ModuleCat.{0} R) ((covers).obj.obj k)).obj
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) :=
  (constantAssociatedTrivializationOfSplitting J ((covers).action k)
    (etaleTorsorSectionSplitting X _ ((covers).action k) (coverProperty k) R)).app
      ((coefficients).action k)

local notation "trivialization" => cmHarrisCoefficientSystemTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid

/-- The trivialization is the canonical invariant-section evaluation map. -/
@[simp] theorem cmHarrisCoefficientSystemTrivialization_hom (k : ℕᵒᵖ) :
    ((trivialization) k).hom =
      associatedEvaluation J ((covers).action k) (constantAction k) := rfl

/-- Evaluation localizes the invariant inclusion and restricts to the tautological graph. -/
theorem cmHarrisCoefficientSystemTrivialization_hom_eq (k : ℕᵒᵖ) :
    ((trivialization) k).hom =
      ((J).overPullback (ModuleCat.{0} R) ((covers).obj.obj k)).map ((inc) k) ≫
        productEvaluation J ((covers).action k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
