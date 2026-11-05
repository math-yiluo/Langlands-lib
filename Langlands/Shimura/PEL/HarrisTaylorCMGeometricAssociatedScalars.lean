import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedSystem
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientScalars

/-! # Quotient-ring coefficients on the exact geometric CM torsors -/

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
local notation "torsor" k => cmHarrisGeometricCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k

local notation "system" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "quotientAction" k => cmHarrisCoefficientAction D ρ p U m hm k

/-- The original full quotient-ring coefficient action, associated directly
on the exact geometric full-kernel torsor. -/
def cmHarrisGeometricAssociatedCoefficientSheaf (k : ℕ) :
    Sheaf J (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k)) :=
  (etaleAssociatedFunctor X (torsor k).val).obj (quotientAction k)

local notation "quotientSheaf" k => cmHarrisGeometricAssociatedCoefficientSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k

/-- The invariant inclusion in quotient-valued sections on the same exact cover. -/
def cmHarrisGeometricAssociatedCoefficientInclusion (k : ℕ) :
    (quotientSheaf k) ⟶
      (productSheaf J (torsor k).val.V).obj
        ((constantSheaf J (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k))).obj
          (quotientAction k).V) :=
  etaleAssociatedInclusion X (torsor k).val (quotientAction k)

local notation "quotientInclusion" k => cmHarrisGeometricAssociatedCoefficientInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k
local notation "systemInclusion" k => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k
local notation "quotientMap" k => Ideal.Quotient.mk (harrisCoefficientScalarIdeal K p m ^ k)

local notation "quotientConstantAction" k =>
  Functor.obj (Functor.mapAction
    (constantSheaf J (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k)))
    (SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k)))
      (quotientAction k)

instance cmHarrisGeometricAssociatedCoefficientInclusion_mono (k : ℕ) :
    Mono (quotientInclusion k) :=
  etaleAssociatedInclusion_mono X (torsor k).val (quotientAction k)

/-- The direct quotient sheaf satisfies the unchanged diagonal invariance law. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientInclusion_invariant (k : ℕ)
    (g : SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k)) :
    (quotientInclusion k) ≫ (diagonal J (torsor k).val (quotientConstantAction k)).ρ g =
      (quotientInclusion k) :=
  inclusion_invariant J (torsor k).val (quotientConstantAction k) g

/-- Quotient-ring invariant evaluation on the exact geometric cover is invertible. -/
def cmHarrisGeometricAssociatedCoefficientTrivialization (k : ℕ) :
    ((J).overPullback (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k))
        (torsor k).val.V).obj (quotientSheaf k) ≅
      ((J).overPullback (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k))
        (torsor k).val.V).obj
        ((constantSheaf J (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k))).obj
          (quotientAction k).V) :=
  (constantAssociatedTrivializationOfSplitting J (torsor k).val
    (etaleTorsorSectionSplitting X _ (torsor k).val (torsor k).property
      (HarrisCoefficientReductionRing K p m k))).app (quotientAction k)

local notation "quotientTrivialization" k =>
  cmHarrisGeometricAssociatedCoefficientTrivialization D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k

/-- The local isomorphism uses the actual invariant inclusion and evaluation. -/
@[simp] theorem cmHarrisGeometricAssociatedCoefficientTrivialization_hom (k : ℕ) :
    (quotientTrivialization k).hom =
      ((J).overPullback (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k))
        (torsor k).val.V).map (quotientInclusion k) ≫
        productEvaluation J (torsor k).val
          ((constantSheaf J (ModuleCat.{0} (HarrisCoefficientReductionRing K p m k))).obj
            (quotientAction k).V) := rfl

/-- Each direct geometric quotient-ring coefficient sheaf, viewed over the integral
ring, is canonically the component of the constructed full inverse system. -/
def cmHarrisGeometricAssociatedCoefficientSheafRestrictIso (k : ℕ) :
    (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).obj (quotientSheaf k) ≅
      (system).obj (op k) :=
  (constantAssociatedRestrictScalarsIso J (quotientMap k) (torsor k).val).app
      (quotientAction k) ≪≫
    (etaleAssociatedFunctor X (torsor k).val).mapIso
      (cmHarrisCoefficientActionRestrictIso D U ρ p m hm k)

local notation "sheafComparison" k => cmHarrisGeometricAssociatedCoefficientSheafRestrictIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k

/-- The comparison preserves the quotient-ring invariant inclusion, with the
canonical constant-module scalar comparison on cover sections. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_hom_inclusion (k : ℕ) :
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
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_inv_inclusion (k : ℕ) :
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

/-- The direct geometric quotient-ring sheaves form an inverse system after restriction
to the fixed integral ring, by transport of the constructed CM transitions. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  (system).copyObj
    (fun k => (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k.unop))).obj
      (quotientSheaf k.unop))
    (fun k => (sheafComparison k.unop).symm)

local notation "restrictedSystem" => cmHarrisGeometricAssociatedRestrictedCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Every component is the direct geometric sheaf with its actual scalars restricted. -/
@[simp] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSystem_obj (k : ℕᵒᵖ) :
    (restrictedSystem).obj k =
      (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k.unop))).obj
        (quotientSheaf k.unop) := rfl

/-- The transition is conjugation of the original integral-system transition. -/
@[simp] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSystem_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (restrictedSystem).map f =
      (sheafComparison i.unop).hom ≫ (system).map f ≫
        (sheafComparison j.unop).inv := rfl

/-- The scalar comparisons form a natural isomorphism of the complete inverse
systems, including every exact geometric coefficient-kernel transition. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSystemIso : (restrictedSystem) ≅ (system) :=
  ((system).isoCopyObj
    (fun k => (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k.unop))).obj
      (quotientSheaf k.unop))
    (fun k => (sheafComparison k.unop).symm)).symm

/-- The natural-system comparison has exactly the original scalar component. -/
@[simp] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSystemIso_app (k : ℕᵒᵖ) :
    (cmHarrisGeometricAssociatedRestrictedCoefficientSystemIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid).app k =
      (sheafComparison k.unop) := rfl

local notation "localize" k => (J).overPullback (ModuleCat.{0} R) (torsor k).val.V
local notation "localRestrict" k => sheafCompose ((J).over (torsor k).val.V)
  (ModuleCat.restrictScalars.{0} (quotientMap k))
local notation "originalTrivialization" k => quotientTrivialization k
local notation "integralTrivialization" k =>
  cmHarrisGeometricAssociatedCoefficientTrivializationAlong D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid (op k) (𝟙 _)
local notation "constantComparison" k =>
  (constantRestrictScalarsIso J (quotientMap k)).app (quotientAction k).V

/-- Restrict the direct geometric quotient-ring evaluation trivialization to integral
scalars, then use the canonical comparison of constant coefficient sheaves. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientTrivialization (k : ℕ) :
    (localize k).obj
        ((sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).obj
          (quotientSheaf k)) ≅
      (localize k).obj
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj (op k))) :=
  (localRestrict k).mapIso (originalTrivialization k) ≪≫
    (localize k).mapIso (constantComparison k)

local notation "restrictedTrivialization" k => cmHarrisGeometricAssociatedRestrictedCoefficientTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k

/-- This is the quotient-ring local evaluation after scalar restriction and the
canonical constant-coefficient comparison. -/
theorem cmHarrisGeometricAssociatedRestrictedCoefficientTrivialization_hom (k : ℕ) :
    (restrictedTrivialization k).hom =
      (localRestrict k).map (originalTrivialization k).hom ≫
        (localize k).map (constantComparison k).hom := rfl

/-- The actual global scalar comparison preserves tautological local evaluation. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_hom_trivialization (k : ℕ) :
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
  have hi := cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_hom_inclusion D C preservation
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
theorem cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_trivialization (k : ℕ) :
    (localize k).mapIso (sheafComparison k) ≪≫ (integralTrivialization k) =
      (restrictedTrivialization k) := by
  apply Iso.ext
  exact cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_hom_trivialization D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k

/-- The inverse global comparison also preserves the quotient-ring local evaluation. -/
@[reassoc] theorem cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_inv_trivialization (k : ℕ) :
    (localize k).map (sheafComparison k).inv ≫ (restrictedTrivialization k).hom =
      (integralTrivialization k).hom := by
  rw [← cmHarrisGeometricAssociatedCoefficientSheafRestrictIso_hom_trivialization D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, (localize k).map_id, Category.id_comp]


local notation "systemComparison" =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSystemIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid
local notation "sourceTrivialization" k =>
  cmHarrisGeometricAssociatedCoefficientSourceTrivialization D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k
local notation "constantSource" k =>
  cmHarrisGeometricConstantCoefficientSourceSystem D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k
local notation "sourceLocalize" k => (J).overPullback (ModuleCat.{0} R) ((covers).obj.obj k)

/-- The directly associated quotient sheaves, restricted to integral scalars and
localized together on the exact source cover. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} R) :=
  Under.forget k ⋙ restrictedSystem ⋙ sourceLocalize k

local notation "restrictedSource" k =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k

/-- Scalar restriction followed by the proved source-cover evaluation compares
the whole reachable diagram with the unchanged constant coefficient diagram. -/
def cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization (k : ℕᵒᵖ) :
    (restrictedSource k) ≅ (constantSource k) :=
  Functor.isoWhiskerLeft (Under.forget k)
      (Functor.isoWhiskerRight systemComparison (sourceLocalize k)) ≪≫
    (sourceTrivialization k)

local notation "restrictedSourceTrivialization" k =>
  cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k

/-- Every component is the actual scalar comparison followed by evaluation
along the exact geometric forgetting map from the source cover. -/
@[simp] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    (restrictedSourceTrivialization k).hom.app i =
      (sourceLocalize k).map (sheafComparison i.right.unop).hom ≫
        etaleAssociatedEvaluationAlong X covers coefficients i.right
          ((covers).obj.map i.hom) := rfl

/-- All transported transitions become the original full-lattice coefficient
reductions under this simultaneous source-cover trivialization. -/
@[reassoc] theorem cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    (sourceLocalize k).map ((restrictedSystem).map f.right) ≫
        (restrictedSourceTrivialization k).hom.app j =
      (restrictedSourceTrivialization k).hom.app i ≫
        (sourceLocalize k).map
          ((constantSheaf J (ModuleCat.{0} R)).map ((coefficients).obj.map f.right)) :=
  (restrictedSourceTrivialization k).hom.naturality f


end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
