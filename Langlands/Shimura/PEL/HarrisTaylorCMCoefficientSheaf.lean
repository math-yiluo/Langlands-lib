import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientReduction
import Langlands.Shimura.PEL.HarrisTaylorCMNormalSmoothTorsor
import Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof
import Langlands.Shimura.Coefficients.EtaleCoverComparisonProof
import Langlands.Shimura.Coefficients.TrivializationFromSplitting

/-! # Full Harris torsion coefficient sheaves on original CM scheme levels -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})

variable (hRigid : CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor U.obj)

variable
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0) (k : ℕ)

local notation "X" => Functor.obj (schemes q) U
local notation "Vcoeff" => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "Rcoeff" => HarrisCoefficientReductionRing K p m k
local notation "Mcoeff" => cmHarrisCoefficientAction D ρ p U m hm k
local notation "J" => Scheme.smallEtaleTopology X

/-- The original CM torsor at the constructed full coefficient kernel level.
The generic dominant criterion is discharged by its published proof. -/
def cmHarrisCoefficientTorsor :
    {Y : Action (X).Etale (SmallCMResidualGroup D U Vcoeff) //
      IsFiniteGeometricTorsor X Y} :=
  cmNormalGeometricTorsor_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor U Vcoeff
    (cmHarrisCoefficientLevel_le D ρ p U m hm k) q existence geometry hRigid
    DominantUnramifiedEtaleProof.dominantUnramifiedEtale

local notation "torsor" => cmHarrisCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

/-- Its fine scheme is the original chosen CM scheme at the actual kernel level. -/
@[simp] theorem cmHarrisCoefficientTorsor_left :
    (torsor).val.V.left = (schemes q).obj Vcoeff := rfl

/-- Its structural morphism is the original forgetting map in the chosen tower. -/
@[simp] theorem cmHarrisCoefficientTorsor_hom :
    (torsor).val.V.hom =
      (schemes q).map (smallCMInclusion D (cmHarrisCoefficientLevel_le D ρ p U m hm k)) := rfl

/-- No replacement deck action is introduced by the coefficient specialization. -/
@[simp] theorem cmHarrisCoefficientTorsor_ρ_left
    (g : SmallCMResidualGroup D U Vcoeff) :
    ((torsor).val.ρ g).left =
      (cmNormalQuotientAction D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U Vcoeff
        (cmHarrisCoefficientLevel_le D ρ p U m hm k) q).ρ g := rfl

/-- The actual coefficient cover covers the final object of the small etale site. -/
theorem cmHarrisCoefficientTorsor_coversTop :
    (J).CoversTop (fun _ : Unit => (torsor).val.V) :=
  etale_coversTop_of_surjective (torsor).val.V (torsor).property.2.2.1

/-- The full torsion coefficient sheaf on the original chosen CM coarse scheme. -/
def cmHarrisCoefficientSheaf : Sheaf J (ModuleCat.{0} Rcoeff) :=
  (etaleAssociatedFunctor X (torsor).val).obj Mcoeff

local notation "coefficientSheaf" => cmHarrisCoefficientSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
set_option quotPrecheck false in
local notation "constantAction" =>
  Functor.obj (Functor.mapAction (constantSheaf J (ModuleCat.{0} Rcoeff))
    (SmallCMResidualGroup D U Vcoeff)) Mcoeff

/-- The constructed sheaf is included in coefficient sections over the original cover. -/
def cmHarrisCoefficientInclusion :
    coefficientSheaf ⟶
      (productSheaf J (torsor).val.V).obj ((constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V) :=
  inclusion J (torsor).val constantAction

local notation "coefficientInclusion" => cmHarrisCoefficientInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

/-- Its sections satisfy the actual diagonal coefficient and inverse-deck invariance. -/
@[reassoc] theorem cmHarrisCoefficientInclusion_invariant
    (g : SmallCMResidualGroup D U Vcoeff) :
    coefficientInclusion ≫ (diagonal J (torsor).val constantAction).ρ g = coefficientInclusion :=
  inclusion_invariant J (torsor).val constantAction g

/-- Restriction to the actual coefficient cover is canonically trivialized by
invariant-section evaluation, using the proved geometric graph splitting. -/
def cmHarrisCoefficientTrivialization :
    ((J).overPullback (ModuleCat.{0} Rcoeff) (torsor).val.V).obj coefficientSheaf ≅
      ((J).overPullback (ModuleCat.{0} Rcoeff) (torsor).val.V).obj
        ((constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V) :=
  (constantAssociatedTrivializationOfSplitting J (torsor).val
    (etaleTorsorSectionSplitting X _ (torsor).val (torsor).property Rcoeff)).app Mcoeff

local notation "trivialization" => cmHarrisCoefficientTrivialization D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

/-- The local isomorphism uses precisely the canonical invariant-section evaluation map. -/
@[simp] theorem cmHarrisCoefficientTrivialization_hom :
    (trivialization).hom = associatedEvaluation J (torsor).val constantAction := rfl

/-- Evaluation is the localized invariant inclusion followed by tautological graph restriction. -/
theorem cmHarrisCoefficientTrivialization_hom_eq :
    (trivialization).hom =
      ((J).overPullback (ModuleCat.{0} Rcoeff) (torsor).val.V).map coefficientInclusion ≫
        productEvaluation J (torsor).val ((constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V) := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
