import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCohomology
import Mathlib.CategoryTheory.Action.Limits

/-! # Galois-equivariant normalized finite shifts of CM coefficients -/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Cohomology Langlands.Geometry
open EtaleInverseImage EtaleGeometricDiagram
open scoped CategoryTheory.Prod

private theorem cmGaloisNatIso_conjugate
    {C₀ D₀ E₀ : Type*} [Category C₀] [Category D₀] [Category E₀]
    (F₀ : C₀ ⥤ D₀) (H₀ : D₀ ⥤ E₀) (G₀ : C₀ ⥤ E₀)
    (I : F₀ ⋙ H₀ ≅ G₀) {X Y : C₀} (f : X ⟶ Y) :
    I.inv.app X ≫ H₀.map (F₀.map f) ≫ I.hom.app Y = G₀.map f := by
  change I.inv.app X ≫ (F₀ ⋙ H₀).map f ≫ I.hom.app Y = _
  rw [I.hom.naturality, ← Category.assoc, I.inv_hom_id_app, Category.id_comp]

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

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "galoisMap" => cmGeometricGaloisMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

variable (U : SmallCMLevel D)

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "g" σ:max => (galoisMap σ).app U

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "geometricSystem" => cmHarrisGeometricCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coefficientIso" => cmHarrisGeometricCoefficientGaloisIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

private def cmGaloisShiftIndex (k : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show Monotone (fun r : ℕ => r + k) from
    fun _ _ hrs => Nat.add_le_add_right hrs k).functor.op

local notation "shiftInclusion" => cmHarrisGeometricCoefficientShiftInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "shiftReduction" => cmHarrisGeometricCoefficientShiftReduction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "originalInclusion" => cmHarrisCoefficientShiftInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- The original normalized shift inclusions commute with the canonical
Galois coefficient comparison, including shift zero. -/
theorem cmHarrisGeometricCoefficientGaloisIso_shiftInclusion
    (k : ℕ) (r : ℕᵒᵖ) (σ : Galois) :
    (inverseImage (g σ) Rcoeff).map ((shiftInclusion k).app r) ≫
        ((coefficientIso) σ).hom.app (op (r.unop + k)) =
      ((coefficientIso) σ).hom.app r ≫ (shiftInclusion k).app r := by
  simpa only [cmHarrisGeometricCoefficientGaloisIso_hom_app,
    cmHarrisGeometricCoefficientShiftInclusion_app, cmHarrisCoefficientShiftedSystem,
    Functor.comp_obj, Functor.op_obj, Monotone.functor_obj, Functor.comp_map] using
      (cmGeometricGaloisInverseImageIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U Rcoeff σ).hom.naturality
          ((originalInclusion k).app r)

open EtaleDerivedSections EtaleDerivedGlobalPullback

variable [HasDerivedCategory.{wS}
    (ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

local notation "RD" => EtaleDerivedSectionsPlus.derivedSections
  ((geometricSchemes).obj U) Rcoeff
local notation "derivedAction" => cmHarrisGeometricGaloisDerivedAction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "cohomologyAction" => cmHarrisGeometricGaloisCohomologyAction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "sectionsAction" => cmHarrisGeometricGaloisSectionsAction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- Shift the original derived action system by addition of `k` to its exponent. -/
def cmHarrisGeometricGaloisDerivedShiftedAction (k : ℕ) :
    ℕᵒᵖ ⥤ Action (DerivedCategory.Plus (ModuleCat Rcoeff)) Galois :=
  cmGaloisShiftIndex k ⋙ derivedAction

local notation "derivedShiftedAction" => cmHarrisGeometricGaloisDerivedShiftedAction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

private theorem cmGaloisDerivedInclusion_comm (k : ℕ) (r : ℕᵒᵖ) (σ : Galois) :
    ((derivedAction).obj r).ρ σ ≫ (RD).map ((shiftInclusion k).app r) =
      (RD).map ((shiftInclusion k).app r) ≫
        ((derivedAction).obj (op (r.unop + k))).ρ σ := by
  rw [cmHarrisGeometricGaloisDerivedAction_obj_ρ D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    cmHarrisGeometricGaloisDerivedAction_obj_ρ D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    ← sheafDerivedPullbackWithCoefficients_postcomp,
    ← sheafDerivedPullbackWithCoefficients_precomp]
  exact congrArg (fun a => sheafDerivedPullbackWithCoefficients (g σ) Rcoeff a)
    (cmHarrisGeometricCoefficientGaloisIso_shiftInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k r σ).symm

private theorem cmGaloisDerivedInclusion_naturality (k : ℕ)
    {r s : ℕᵒᵖ} (f : r ⟶ s) :
    ((derivedAction).map f).hom ≫ (RD).map ((shiftInclusion k).app s) =
      (RD).map ((shiftInclusion k).app r) ≫
        ((derivedAction).map ((cmGaloisShiftIndex k).map f)).hom := by
  rw [cmHarrisGeometricGaloisDerivedAction_map_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    cmHarrisGeometricGaloisDerivedAction_map_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    ← (RD).map_comp, ← (RD).map_comp]
  exact congrArg (fun a => (RD).map a) ((shiftInclusion k).naturality f)

private def cmGaloisDerivedInclusionComponent (k : ℕ) (r : ℕᵒᵖ) :
    (derivedAction).obj r ⟶ (derivedAction).obj (op (r.unop + k)) where
  hom := (RD).map ((shiftInclusion k).app r)
  comm σ := cmGaloisDerivedInclusion_comm D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k r σ

/-- Derived global sections of the original normalized inclusion define
an equivariant morphism of the original inverse systems. -/
def cmHarrisGeometricGaloisDerivedShiftInclusion (k : ℕ) :
    derivedAction ⟶ derivedShiftedAction k where
  app r := cmGaloisDerivedInclusionComponent D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k r
  naturality _ _ f := Action.Hom.ext
    (cmGaloisDerivedInclusion_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k f)

/-- The reverse equivariant map is the original reduction from exponent `r+k`. -/
def cmHarrisGeometricGaloisDerivedShiftReduction (k : ℕ) :
    derivedShiftedAction k ⟶ derivedAction where
  app r := (derivedAction).map (homOfLE (Nat.le_add_right r.unop k)).op
  naturality r s f := by
    change (derivedAction).map _ ≫ (derivedAction).map _ =
      (derivedAction).map _ ≫ (derivedAction).map _
    rw [← (derivedAction).map_comp, ← (derivedAction).map_comp]
    congr 1


local notation "derivedInclusion" => cmHarrisGeometricGaloisDerivedShiftInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "derivedReduction" => cmHarrisGeometricGaloisDerivedShiftReduction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- The equivariant inclusion retains exactly the original derived coefficient map. -/
@[simp] theorem cmHarrisGeometricGaloisDerivedShiftInclusion_app_hom
    (k : ℕ) (r : ℕᵒᵖ) :
    ((derivedInclusion k).app r).hom = (RD).map ((shiftInclusion k).app r) := rfl

/-- The equivariant reduction retains exactly the original derived coefficient map. -/
@[simp] theorem cmHarrisGeometricGaloisDerivedShiftReduction_app_hom
    (k : ℕ) (r : ℕᵒᵖ) :
    ((derivedReduction k).app r).hom = (RD).map ((shiftReduction k).app r) :=
  cmHarrisGeometricGaloisDerivedAction_map_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
    (homOfLE (Nat.le_add_right r.unop k)).op

local instance cmGaloisDerivedSections_additive : (RD).Additive := by
  dsimp only [EtaleDerivedSectionsPlus.derivedSections, DerivedPlus.derivedComplex]
  infer_instance

/-- The composite on the original derived action system is multiplication by `m^k`. -/
theorem cmHarrisGeometricGaloisDerivedShiftInclusion_reduction (k : ℕ) :
    derivedInclusion k ≫ derivedReduction k = powSMul m k derivedAction := by
  apply NatTrans.ext
  funext r
  apply Action.Hom.ext
  change (RD).map ((shiftInclusion k).app r) ≫ ((derivedReduction k).app r).hom =
    powSMul m k ((RD).obj ((geometricSystem).obj r))
  rw [cmHarrisGeometricGaloisDerivedShiftReduction_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid, ← (RD).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisGeometricCoefficientShiftInclusion_reduction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k)
  change (shiftInclusion k).app r ≫ (shiftReduction k).app r =
    powSMul m k ((geometricSystem).obj r) at heq
  rw [heq]
  exact map_powSMul (RD) m k _

/-- The reverse composite is the same scalar power on the shifted derived action system. -/
theorem cmHarrisGeometricGaloisDerivedShiftReduction_inclusion (k : ℕ) :
    derivedReduction k ≫ derivedInclusion k =
      powSMul m k (derivedShiftedAction k) := by
  apply NatTrans.ext
  funext r
  apply Action.Hom.ext
  change ((derivedReduction k).app r).hom ≫ (RD).map ((shiftInclusion k).app r) =
    powSMul m k ((RD).obj ((geometricSystem).obj (op (r.unop + k))))
  rw [cmHarrisGeometricGaloisDerivedShiftReduction_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid, ← (RD).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisGeometricCoefficientShiftReduction_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k)
  change (shiftReduction k).app r ≫ (shiftInclusion k).app r =
    powSMul m k ((geometricSystem).obj (op (r.unop + k))) at heq
  rw [heq]
  exact map_powSMul (RD) m k _

local notation "homologyIso" => cmHarrisGeometricGaloisDerivedHomologyIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "zeroIso" => cmHarrisGeometricGaloisDerivedZeroIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "H" d => cohomology ((geometricSchemes).obj U) Rcoeff d
local notation "Γ" => sections ((geometricSchemes).obj U) Rcoeff

/-- Shift the original ordinary cohomology action by `k` coefficient exponents. -/
def cmHarrisGeometricGaloisCohomologyShiftedAction (d k : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat Rcoeff) Galois :=
  cmGaloisShiftIndex k ⋙ cohomologyAction d

local notation "cohomologyShiftedAction" => cmHarrisGeometricGaloisCohomologyShiftedAction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- Transport the derived equivariant inclusion through the canonical homology comparison. -/
def cmHarrisGeometricGaloisCohomologyShiftInclusion (d k : ℕ) :
    cohomologyAction d ⟶ cohomologyShiftedAction d k :=
  (homologyIso d).inv ≫
    Functor.whiskerRight (derivedInclusion k)
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) d).mapAction Galois) ≫
    Functor.whiskerLeft (cmGaloisShiftIndex k) (homologyIso d).hom

/-- The reverse ordinary cohomology map is the original equivariant reduction. -/
def cmHarrisGeometricGaloisCohomologyShiftReduction (d k : ℕ) :
    cohomologyShiftedAction d k ⟶ cohomologyAction d where
  app r := (cohomologyAction d).map (homOfLE (Nat.le_add_right r.unop k)).op
  naturality r s f := by
    change (cohomologyAction d).map _ ≫ (cohomologyAction d).map _ =
      (cohomologyAction d).map _ ≫ (cohomologyAction d).map _
    rw [← (cohomologyAction d).map_comp, ← (cohomologyAction d).map_comp]
    congr 1

/-- Shift the original section action by `k` coefficient exponents. -/
def cmHarrisGeometricGaloisSectionsShiftedAction (k : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat Rcoeff) Galois :=
  cmGaloisShiftIndex k ⋙ sectionsAction

local notation "sectionsShiftedAction" => cmHarrisGeometricGaloisSectionsShiftedAction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- Transport the derived equivariant inclusion to actual global sections. -/
def cmHarrisGeometricGaloisSectionsShiftInclusion (k : ℕ) :
    sectionsAction ⟶ sectionsShiftedAction k :=
  (zeroIso).inv ≫
    Functor.whiskerRight (derivedInclusion k)
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) 0).mapAction Galois) ≫
    Functor.whiskerLeft (cmGaloisShiftIndex k) (zeroIso).hom

/-- The reverse section map is the original equivariant reduction. -/
def cmHarrisGeometricGaloisSectionsShiftReduction (k : ℕ) :
    sectionsShiftedAction k ⟶ sectionsAction where
  app r := (sectionsAction).map (homOfLE (Nat.le_add_right r.unop k)).op
  naturality r s f := by
    change (sectionsAction).map _ ≫ (sectionsAction).map _ =
      (sectionsAction).map _ ≫ (sectionsAction).map _
    rw [← (sectionsAction).map_comp, ← (sectionsAction).map_comp]
    congr 1


local notation "cohomologyInclusion" => cmHarrisGeometricGaloisCohomologyShiftInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "cohomologyReduction" => cmHarrisGeometricGaloisCohomologyShiftReduction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "sectionsInclusion" => cmHarrisGeometricGaloisSectionsShiftInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "sectionsReduction" => cmHarrisGeometricGaloisSectionsShiftReduction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- The transported equivariant map is ordinary cohomology of exactly the original inclusion. -/
@[simp] theorem cmHarrisGeometricGaloisCohomologyShiftInclusion_app_hom
    (d k : ℕ) (r : ℕᵒᵖ) :
    ((cohomologyInclusion d k).app r).hom = (H d).map ((shiftInclusion k).app r) := by
  change (EtaleDerivedSectionsPlus.homologyNatIso ((geometricSchemes).obj U) Rcoeff d).inv.app
      ((geometricSystem).obj r) ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) d).map
      ((RD).map ((shiftInclusion k).app r)) ≫
    (EtaleDerivedSectionsPlus.homologyNatIso ((geometricSchemes).obj U) Rcoeff d).hom.app
      ((geometricSystem).obj (op (r.unop + k))) = _
  exact cmGaloisNatIso_conjugate (RD)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) d) (H d)
    (EtaleDerivedSectionsPlus.homologyNatIso ((geometricSchemes).obj U) Rcoeff d)
    ((shiftInclusion k).app r)

/-- The equivariant ordinary reduction is cohomology of the original reduction. -/
@[simp] theorem cmHarrisGeometricGaloisCohomologyShiftReduction_app_hom
    (d k : ℕ) (r : ℕᵒᵖ) :
    ((cohomologyReduction d k).app r).hom = (H d).map ((shiftReduction k).app r) :=
  cmHarrisGeometricGaloisCohomologyAction_map_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid d
    (homOfLE (Nat.le_add_right r.unop k)).op

/-- The transported section map is actual global sections of the original inclusion. -/
@[simp] theorem cmHarrisGeometricGaloisSectionsShiftInclusion_app_hom
    (k : ℕ) (r : ℕᵒᵖ) :
    ((sectionsInclusion k).app r).hom = (Γ).map ((shiftInclusion k).app r) := by
  change (EtaleDerivedSectionsPlus.homologyZeroIso ((geometricSchemes).obj U) Rcoeff).inv.app
      ((geometricSystem).obj r) ≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) 0).map
      ((RD).map ((shiftInclusion k).app r)) ≫
    (EtaleDerivedSectionsPlus.homologyZeroIso ((geometricSchemes).obj U) Rcoeff).hom.app
      ((geometricSystem).obj (op (r.unop + k))) = _
  exact cmGaloisNatIso_conjugate (RD)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) 0) (Γ)
    (EtaleDerivedSectionsPlus.homologyZeroIso ((geometricSchemes).obj U) Rcoeff)
    ((shiftInclusion k).app r)

/-- The equivariant section reduction is actual sections of the original reduction. -/
@[simp] theorem cmHarrisGeometricGaloisSectionsShiftReduction_app_hom
    (k : ℕ) (r : ℕᵒᵖ) :
    ((sectionsReduction k).app r).hom = (Γ).map ((shiftReduction k).app r) :=
  cmHarrisGeometricGaloisSectionsAction_map_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
    (homOfLE (Nat.le_add_right r.unop k)).op

local instance cmGaloisCohomology_additive (d : ℕ) : (H d).Additive :=
  Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive
    (sections ((geometricSchemes).obj U) Rcoeff) d

/-- The ordinary action-system composite on the original coefficients is `m^k`. -/
theorem cmHarrisGeometricGaloisCohomologyShiftInclusion_reduction (d k : ℕ) :
    cohomologyInclusion d k ≫ cohomologyReduction d k =
      powSMul m k (cohomologyAction d) := by
  apply NatTrans.ext
  funext r
  apply Action.Hom.ext
  change ((cohomologyInclusion d k).app r).hom ≫ ((cohomologyReduction d k).app r).hom =
    powSMul m k ((H d).obj ((geometricSystem).obj r))
  rw [cmHarrisGeometricGaloisCohomologyShiftInclusion_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    cmHarrisGeometricGaloisCohomologyShiftReduction_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid, ← (H d).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisGeometricCoefficientShiftInclusion_reduction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k)
  change (shiftInclusion k).app r ≫ (shiftReduction k).app r =
    powSMul m k ((geometricSystem).obj r) at heq
  rw [heq]
  exact map_powSMul (H d) m k _

/-- The reverse ordinary composite is `m^k` on the shifted action system. -/
theorem cmHarrisGeometricGaloisCohomologyShiftReduction_inclusion (d k : ℕ) :
    cohomologyReduction d k ≫ cohomologyInclusion d k =
      powSMul m k (cohomologyShiftedAction d k) := by
  apply NatTrans.ext
  funext r
  apply Action.Hom.ext
  change ((cohomologyReduction d k).app r).hom ≫ ((cohomologyInclusion d k).app r).hom =
    powSMul m k ((H d).obj ((geometricSystem).obj (op (r.unop + k))))
  rw [cmHarrisGeometricGaloisCohomologyShiftReduction_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    cmHarrisGeometricGaloisCohomologyShiftInclusion_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid, ← (H d).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisGeometricCoefficientShiftReduction_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k)
  change (shiftReduction k).app r ≫ (shiftInclusion k).app r =
    powSMul m k ((geometricSystem).obj (op (r.unop + k))) at heq
  rw [heq]
  exact map_powSMul (H d) m k _

/-- Inclusion followed by reduction is `m^k` on the original section action system. -/
theorem cmHarrisGeometricGaloisSectionsShiftInclusion_reduction (k : ℕ) :
    sectionsInclusion k ≫ sectionsReduction k = powSMul m k sectionsAction := by
  apply NatTrans.ext
  funext r
  apply Action.Hom.ext
  change ((sectionsInclusion k).app r).hom ≫ ((sectionsReduction k).app r).hom =
    powSMul m k ((Γ).obj ((geometricSystem).obj r))
  rw [cmHarrisGeometricGaloisSectionsShiftInclusion_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    cmHarrisGeometricGaloisSectionsShiftReduction_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid, ← (Γ).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisGeometricCoefficientShiftInclusion_reduction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k)
  change (shiftInclusion k).app r ≫ (shiftReduction k).app r =
    powSMul m k ((geometricSystem).obj r) at heq
  rw [heq]
  exact map_powSMul (Γ) m k _

/-- The reverse composite is `m^k` on the shifted section action system. -/
theorem cmHarrisGeometricGaloisSectionsShiftReduction_inclusion (k : ℕ) :
    sectionsReduction k ≫ sectionsInclusion k =
      powSMul m k (sectionsShiftedAction k) := by
  apply NatTrans.ext
  funext r
  apply Action.Hom.ext
  change ((sectionsReduction k).app r).hom ≫ ((sectionsInclusion k).app r).hom =
    powSMul m k ((Γ).obj ((geometricSystem).obj (op (r.unop + k))))
  rw [cmHarrisGeometricGaloisSectionsShiftReduction_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    cmHarrisGeometricGaloisSectionsShiftInclusion_app_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid, ← (Γ).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisGeometricCoefficientShiftReduction_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k)
  change (shiftReduction k).app r ≫ (shiftInclusion k).app r =
    powSMul m k ((geometricSystem).obj (op (r.unop + k))) at heq
  rw [heq]
  exact map_powSMul (Γ) m k _

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
