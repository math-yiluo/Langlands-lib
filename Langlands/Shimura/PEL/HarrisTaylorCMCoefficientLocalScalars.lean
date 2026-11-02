import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientScalars

/-! # Scalar-compatible local evaluation for original CM coefficient sheaves -/

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

local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "quotientAction" k => cmHarrisCoefficientAction D ρ p U m hm k
local notation "quotientSheaf" k => cmHarrisCoefficientSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "quotientInclusion" k => cmHarrisCoefficientInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "systemInclusion" k => cmHarrisCoefficientSystemInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k
local notation "quotientMap" k => Ideal.Quotient.mk (harrisCoefficientScalarIdeal K p m ^ k)


local notation "sheafComparison" k => cmHarrisCoefficientSheafRestrictIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k
local notation "localize" k => (J).overPullback (ModuleCat.{0} R) (torsor k).val.V
local notation "localRestrict" k => sheafCompose ((J).over (torsor k).val.V)
  (ModuleCat.restrictScalars.{0} (quotientMap k))
local notation "originalTrivialization" k => cmHarrisCoefficientTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k
local notation "integralTrivialization" k => cmHarrisCoefficientSystemTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid (op k)
local notation "constantComparison" k =>
  (constantRestrictScalarsIso J (quotientMap k)).app (quotientAction k).V

/-- Restrict the original quotient-ring evaluation trivialization to integral
scalars, then use the canonical comparison of constant coefficient sheaves. -/
def cmHarrisRestrictedCoefficientTrivialization (k : ℕ) :
    (localize k).obj
        ((sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).obj
          (quotientSheaf k)) ≅
      (localize k).obj
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj (op k))) :=
  (localRestrict k).mapIso (originalTrivialization k) ≪≫
    (localize k).mapIso (constantComparison k)

local notation "restrictedTrivialization" k => cmHarrisRestrictedCoefficientTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k

/-- This is the original local evaluation after scalar restriction and the
canonical constant-coefficient comparison. -/
theorem cmHarrisRestrictedCoefficientTrivialization_hom (k : ℕ) :
    (restrictedTrivialization k).hom =
      (localRestrict k).map (originalTrivialization k).hom ≫
        (localize k).map (constantComparison k).hom := rfl

/-- The actual global scalar comparison preserves tautological local evaluation. -/
@[reassoc] theorem cmHarrisCoefficientSheafRestrictIso_hom_trivialization (k : ℕ) :
    (localize k).map (sheafComparison k).hom ≫ (integralTrivialization k).hom =
      (restrictedTrivialization k).hom := by
  let loc := localize k
  let c := (constantComparison k).hom
  let F := (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).obj
    ((constantSheaf J
      (ModuleCat.{0} (R ⧸ harrisCoefficientScalarIdeal K p m ^ k))).obj
        (quotientAction k).V)
  let F' := (constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj (op k))
  let a := (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).map
    (quotientInclusion k)
  have hi := cmHarrisCoefficientSheafRestrictIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k
  have hi' := congrArg (fun f => loc.map f) hi
  have hi'' := ((loc.map_comp _ _).symm.trans hi').trans (loc.map_comp _ _)
  have hn := productEvaluation_natural J (torsor k).val c
  change loc.map (sheafComparison k).hom ≫
      (loc.map (systemInclusion (op k)) ≫ productEvaluation J (torsor k).val F') = _
  calc
    _ = (loc.map (sheafComparison k).hom ≫ loc.map (systemInclusion (op k))) ≫
        productEvaluation J (torsor k).val F' := (Category.assoc _ _ _).symm
    _ = (loc.map a ≫ loc.map ((productSheaf J (torsor k).val.V).map c)) ≫
        productEvaluation J (torsor k).val F' :=
      congrArg (fun f => f ≫ productEvaluation J (torsor k).val F') hi''
    _ = loc.map a ≫ (loc.map ((productSheaf J (torsor k).val.V).map c) ≫
        productEvaluation J (torsor k).val F') := Category.assoc _ _ _
    _ = loc.map a ≫ (productEvaluation J (torsor k).val F ≫ loc.map c) :=
      congrArg (fun f => loc.map a ≫ f) hn
    _ = _ := (Category.assoc _ _ _).symm

/-- The complete isomorphisms agree, including their inverse local maps. -/
theorem cmHarrisCoefficientSheafRestrictIso_trivialization (k : ℕ) :
    (localize k).mapIso (sheafComparison k) ≪≫ (integralTrivialization k) =
      (restrictedTrivialization k) := by
  apply Iso.ext
  exact cmHarrisCoefficientSheafRestrictIso_hom_trivialization D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k

/-- The inverse global comparison also preserves the original local evaluation. -/
@[reassoc] theorem cmHarrisCoefficientSheafRestrictIso_inv_trivialization (k : ℕ) :
    (localize k).map (sheafComparison k).inv ≫ (restrictedTrivialization k).hom =
      (integralTrivialization k).hom := by
  rw [← cmHarrisCoefficientSheafRestrictIso_hom_trivialization D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, (localize k).map_id, Category.id_comp]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
