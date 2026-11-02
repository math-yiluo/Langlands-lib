import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSystem
import Langlands.Shimura.Coefficients.ConstantScalarRestriction

/-! # Quotient-ring and integral-scalar Harris coefficient sheaves -/

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

/-- Scalar restriction identifies the original quotient-ring action with the
actual integral coefficient-diagram action, by the identity on the quotient. -/
def cmHarrisCoefficientActionRestrictIso (k : ℕ) :
    ((ModuleCat.restrictScalars.{0} (quotientMap k)).mapAction
      (SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k))).obj
        (quotientAction k) ≅ (coefficients).action (op k) :=
  Action.mkIso (Iso.refl _) (by
    intro g
    apply ModuleCat.hom_ext
    ext x
    exact (cmHarrisCoefficientDiagram_action D ρ p U m hm k g x).symm)

/-- The underlying coefficient comparison is exactly the identity map. -/
@[simp] theorem cmHarrisCoefficientActionRestrictIso_hom_hom (k : ℕ) :
    (cmHarrisCoefficientActionRestrictIso D U ρ p m hm k).hom.hom = 𝟙 _ := rfl

/-- The inverse coefficient comparison is also exactly the identity map. -/
@[simp] theorem cmHarrisCoefficientActionRestrictIso_inv_hom (k : ℕ) :
    (cmHarrisCoefficientActionRestrictIso D U ρ p m hm k).inv.hom = 𝟙 _ := rfl

/-- Each original quotient-ring coefficient sheaf, viewed over the integral
ring, is canonically the component of the constructed full inverse system. -/
def cmHarrisCoefficientSheafRestrictIso (k : ℕ) :
    (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).obj (quotientSheaf k) ≅
      (system).obj (op k) :=
  (constantAssociatedRestrictScalarsIso J (quotientMap k) (torsor k).val).app
      (quotientAction k) ≪≫
    (etaleAssociatedFunctor X (torsor k).val).mapIso
      (cmHarrisCoefficientActionRestrictIso D U ρ p m hm k)

local notation "sheafComparison" k => cmHarrisCoefficientSheafRestrictIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k

/-- The comparison preserves the original invariant inclusion, with the
canonical constant-module scalar comparison on cover sections. -/
@[reassoc] theorem cmHarrisCoefficientSheafRestrictIso_hom_inclusion (k : ℕ) :
    (sheafComparison k).hom ≫ (systemInclusion (op k)) =
      (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).map
          (quotientInclusion k) ≫
        (productSheaf J (torsor k).val.V).map
          ((constantRestrictScalarsIso J (quotientMap k)).hom.app (quotientAction k).V) := by
  let e := (constantAssociatedRestrictScalarsIso J (quotientMap k) (torsor k).val).app
    (quotientAction k)
  let c := cmHarrisCoefficientActionRestrictIso D U ρ p m hm k
  have hn := etaleAssociatedInclusion_natural X (torsor k).val c.hom
  change (etaleAssociatedFunctor X (torsor k).val).map c.hom ≫
      etaleAssociatedInclusion X (torsor k).val ((coefficients).action (op k)) =
    etaleAssociatedInclusion X (torsor k).val
      (((ModuleCat.restrictScalars.{0} (quotientMap k)).mapAction _).obj (quotientAction k)) ≫
      (productSheaf J (torsor k).val.V).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hn
  have hp := congrArg (fun a => (productSheaf J (torsor k).val.V).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      ((ModuleCat.restrictScalars.{0} (quotientMap k)).obj (quotientAction k).V))
  have hp' := hp.trans ((productSheaf J (torsor k).val.V).map_id _)
  have hn' := hn.trans ((congrArg (fun a =>
    etaleAssociatedInclusion X (torsor k).val
      (((ModuleCat.restrictScalars.{0} (quotientMap k)).mapAction _).obj (quotientAction k)) ≫ a)
    hp').trans (Category.comp_id _))
  exact (Category.assoc e.hom _ _).trans
    ((congrArg (fun a => e.hom ≫ a) hn').trans
      (constantAssociatedRestrictScalarsIso_hom_inclusion J (quotientMap k)
        (torsor k).val (quotientAction k)))

/-- The inverse comparison has the corresponding invariant-inclusion formula. -/
@[reassoc] theorem cmHarrisCoefficientSheafRestrictIso_inv_inclusion (k : ℕ) :
    (sheafComparison k).inv ≫
        (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).map
          (quotientInclusion k) =
      (systemInclusion (op k)) ≫ (productSheaf J (torsor k).val.V).map
        ((constantRestrictScalarsIso J (quotientMap k)).inv.app (quotientAction k).V) := by
  let e := (constantAssociatedRestrictScalarsIso J (quotientMap k) (torsor k).val).app
    (quotientAction k)
  let c := cmHarrisCoefficientActionRestrictIso D U ρ p m hm k
  have hn := etaleAssociatedInclusion_natural X (torsor k).val c.inv
  change (etaleAssociatedFunctor X (torsor k).val).map c.inv ≫
      etaleAssociatedInclusion X (torsor k).val
        (((ModuleCat.restrictScalars.{0} (quotientMap k)).mapAction _).obj (quotientAction k)) =
    etaleAssociatedInclusion X (torsor k).val ((coefficients).action (op k)) ≫
      (productSheaf J (torsor k).val.V).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hn
  have hp := congrArg (fun a => (productSheaf J (torsor k).val.V).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id ((coefficients).action (op k)).V)
  have hp' := hp.trans ((productSheaf J (torsor k).val.V).map_id _)
  have hn' := hn.trans ((congrArg (fun a =>
    etaleAssociatedInclusion X (torsor k).val ((coefficients).action (op k)) ≫ a)
    hp').trans (Category.comp_id _))
  have he := constantAssociatedRestrictScalarsIso_inv_inclusion J (quotientMap k)
    (torsor k).val (quotientAction k)
  exact (Category.assoc _ e.inv _).trans
    ((congrArg (fun a => (etaleAssociatedFunctor X (torsor k).val).map c.inv ≫ a) he).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ (productSheaf J (torsor k).val.V).map
          ((constantRestrictScalarsIso J (quotientMap k)).inv.app (quotientAction k).V)) hn')))

/-- The original quotient-ring sheaves form an inverse system after restriction
to the fixed integral ring, by transport of the constructed CM transitions. -/
def cmHarrisRestrictedCoefficientSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  (system).copyObj
    (fun k => (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k.unop))).obj
      (quotientSheaf k.unop))
    (fun k => (sheafComparison k.unop).symm)

local notation "restrictedSystem" => cmHarrisRestrictedCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Every component is the original sheaf with its actual scalars restricted. -/
@[simp] theorem cmHarrisRestrictedCoefficientSystem_obj (k : ℕᵒᵖ) :
    (restrictedSystem).obj k =
      (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k.unop))).obj
        (quotientSheaf k.unop) := rfl

/-- The transition is conjugation of the original integral-system transition. -/
@[simp] theorem cmHarrisRestrictedCoefficientSystem_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (restrictedSystem).map f =
      (sheafComparison i.unop).hom ≫ (system).map f ≫
        (sheafComparison j.unop).inv := rfl

/-- The scalar comparisons form a natural isomorphism of the complete inverse
systems, including every original coefficient-kernel transition. -/
def cmHarrisRestrictedCoefficientSystemIso : (restrictedSystem) ≅ (system) :=
  ((system).isoCopyObj
    (fun k => (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k.unop))).obj
      (quotientSheaf k.unop))
    (fun k => (sheafComparison k.unop).symm)).symm

/-- The natural-system comparison has exactly the original scalar component. -/
@[simp] theorem cmHarrisRestrictedCoefficientSystemIso_app (k : ℕᵒᵖ) :
    (cmHarrisRestrictedCoefficientSystemIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid).app k =
      (sheafComparison k.unop) := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
