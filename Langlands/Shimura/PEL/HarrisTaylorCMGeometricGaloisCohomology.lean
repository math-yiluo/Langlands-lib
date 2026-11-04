import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisDiagram
import Langlands.Geometry.EtaleGeometricActionDiagram

/-! # Galois actions on original geometric CM torsion cohomology -/

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

local notation "galoisCoefficients" => cmHarrisGeometricGaloisCoefficientDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid


open EtaleDerivedSections EtaleDerivedGlobalPullback

variable [HasDerivedCategory.{wS}
    (ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

local instance cmHarrisGeometricGaloisDerivedInstances :
    (x : ℕᵒᵖ × SingleObj (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) →
      HasDerivedCategory.{wS}
        (ModuleSheaf
          ((cmGeometricGaloisCoefficientSchemes D C preservation composition
            unitCoherence associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor q U).obj x).unop
          (HarrisCoefficientIntegers K p)) :=
  fun _ => inferInstanceAs
    (HasDerivedCategory.{wS}
      (ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p)))

/-- The actual original derived torsion-coefficient inverse system, with
constructed Galois actions and equivariant reductions. -/
def cmHarrisGeometricGaloisDerivedAction :
    ℕᵒᵖ ⥤ Action (DerivedCategory.Plus (ModuleCat Rcoeff)) Galois :=
  (galoisCoefficients).derivedAction

/-- Every original ordinary-cohomology inverse system carries the
constructed Galois actions and equivariant reductions. -/
def cmHarrisGeometricGaloisCohomologyAction (degree : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat Rcoeff) Galois :=
  (galoisCoefficients).cohomologyAction degree

/-- The actual section inverse system carries the same constructed
Galois action and equivariant reductions. -/
def cmHarrisGeometricGaloisSectionsAction :
    ℕᵒᵖ ⥤ Action (ModuleCat Rcoeff) Galois :=
  (galoisCoefficients).sectionsAction

local notation "derivedAction" => cmHarrisGeometricGaloisDerivedAction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "cohomologyAction" => cmHarrisGeometricGaloisCohomologyAction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "sectionsAction" => cmHarrisGeometricGaloisSectionsAction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The derived action is on exactly the original derived global sections. -/
@[simp] theorem cmHarrisGeometricGaloisDerivedAction_obj_V (r : ℕᵒᵖ) :
    ((derivedAction).obj r).V =
      (EtaleDerivedSectionsPlus.derivedSections ((geometricSchemes).obj U) Rcoeff).obj
        ((geometricSystem).obj r) := rfl

/-- The ordinary action is on exactly the original cohomology object. -/
@[simp] theorem cmHarrisGeometricGaloisCohomologyAction_obj_V
    (degree : ℕ) (r : ℕᵒᵖ) :
    (((cohomologyAction) degree).obj r).V =
      (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) Rcoeff degree).obj
        ((geometricSystem).obj r) := rfl

/-- The section action is on exactly the actual original global sections. -/
@[simp] theorem cmHarrisGeometricGaloisSectionsAction_obj_V (r : ℕᵒᵖ) :
    ((sectionsAction).obj r).V =
      (EtaleDerivedSections.sections ((geometricSchemes).obj U) Rcoeff).obj
        ((geometricSystem).obj r) := rfl

/-- Every derived Galois operator is geometric pullback along the actual
raw Galois map with precisely the original coefficient comparison. -/
theorem cmHarrisGeometricGaloisDerivedAction_obj_ρ (r : ℕᵒᵖ) (σ : Galois) :
    ((derivedAction).obj r).ρ σ =
      sheafDerivedPullbackWithCoefficients (g σ) Rcoeff
        (((coefficientIso) σ).hom.app r) := by
  simpa only [cmHarrisGeometricGaloisDerivedAction,
    cmGeometricGaloisCoefficientSchemes_map,
    cmHarrisGeometricGaloisCoefficientDiagram_galois D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid r σ] using
      CoefficientDiagram.derivedAction_obj_ρ (galoisCoefficients) r σ

/-- The ordinary Galois operator uses the same actual raw scheme map
and the unchanged finite-stage coefficient comparison. -/
theorem cmHarrisGeometricGaloisCohomologyAction_obj_ρ
    (degree : ℕ) (r : ℕᵒᵖ) (σ : Galois) :
    (((cohomologyAction) degree).obj r).ρ σ =
      cohomologyPullbackWithCoefficients (g σ) Rcoeff degree
        (((coefficientIso) σ).hom.app r) := by
  simpa only [cmHarrisGeometricGaloisCohomologyAction,
    cmGeometricGaloisCoefficientSchemes_map,
    cmHarrisGeometricGaloisCoefficientDiagram_galois D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid r σ] using
      CoefficientDiagram.cohomologyAction_obj_ρ (galoisCoefficients) degree r σ

/-- The section Galois operator uses the actual raw geometric pullback
with the original coefficient comparison. -/
theorem cmHarrisGeometricGaloisSectionsAction_obj_ρ (r : ℕᵒᵖ) (σ : Galois) :
    ((sectionsAction).obj r).ρ σ =
      sectionsPullbackWithCoefficients (g σ) Rcoeff
        (((coefficientIso) σ).hom.app r) := by
  simpa only [cmHarrisGeometricGaloisSectionsAction,
    cmGeometricGaloisCoefficientSchemes_map,
    cmHarrisGeometricGaloisCoefficientDiagram_galois D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid r σ] using
      CoefficientDiagram.sectionsAction_obj_ρ (galoisCoefficients) r σ

/-- The equivariant derived transition is exactly derived global sections
of the original geometric coefficient reduction. -/
theorem cmHarrisGeometricGaloisDerivedAction_map_hom
    {r s : ℕᵒᵖ} (f : r ⟶ s) :
    ((derivedAction).map f).hom =
      (EtaleDerivedSectionsPlus.derivedSections ((geometricSchemes).obj U) Rcoeff).map
        ((geometricSystem).map f) := by
  change ((galoisCoefficients).derivedAction.map f).hom = _
  rw [CoefficientDiagram.derivedAction_map_hom, SingleObj.id_as_one,
    cmHarrisGeometricGaloisCoefficientDiagram_reduction D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid f,
    sheafDerivedPullbackWithCoefficients_postcomp,
    sheafDerivedPullbackWithCoefficients]
  simpa only [Category.id_comp, cmGeometricGaloisCoefficientSchemes,
    cmHarrisGeometricGaloisCoefficientDiagram, CategoryTheory.prod_id_snd,
    SingleObj.id_as_one, Quiver.Hom.unop_op] using congrArg
    (fun a => a ≫
      (EtaleDerivedSectionsPlus.derivedSections ((geometricSchemes).obj U) Rcoeff).map
        ((geometricSystem).map f))
    (diagramDerivedPullback_id Rcoeff
      (cmGeometricGaloisCoefficientSchemes D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U)
      (r, SingleObj.star Galois) ((geometricSystem).obj r))

/-- The equivariant ordinary transition is exactly ordinary cohomology
of the original geometric coefficient reduction. -/
theorem cmHarrisGeometricGaloisCohomologyAction_map_hom
    (degree : ℕ) {r s : ℕᵒᵖ} (f : r ⟶ s) :
    (((cohomologyAction) degree).map f).hom =
      (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) Rcoeff degree).map
        ((geometricSystem).map f) := by
  change
    (EtaleDerivedSectionsPlus.homologyNatIso
      ((geometricSchemes).obj U) Rcoeff degree).inv.app ((geometricSystem).obj r) ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) degree).map
          (((derivedAction).map f).hom) ≫
        (EtaleDerivedSectionsPlus.homologyNatIso
          ((geometricSchemes).obj U) Rcoeff degree).hom.app ((geometricSystem).obj s) = _
  rw [cmHarrisGeometricGaloisDerivedAction_map_hom D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f]
  have hn := (EtaleDerivedSectionsPlus.homologyNatIso
    ((geometricSchemes).obj U) Rcoeff degree).hom.naturality ((geometricSystem).map f)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The equivariant section transition is exactly actual global sections
of the original geometric coefficient reduction. -/
theorem cmHarrisGeometricGaloisSectionsAction_map_hom
    {r s : ℕᵒᵖ} (f : r ⟶ s) :
    ((sectionsAction).map f).hom =
      (EtaleDerivedSections.sections ((geometricSchemes).obj U) Rcoeff).map
        ((geometricSystem).map f) := by
  change
    (EtaleDerivedSectionsPlus.homologyZeroIso
      ((geometricSchemes).obj U) Rcoeff).inv.app ((geometricSystem).obj r) ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) 0).map
          (((derivedAction).map f).hom) ≫
        (EtaleDerivedSectionsPlus.homologyZeroIso
          ((geometricSchemes).obj U) Rcoeff).hom.app ((geometricSystem).obj s) = _
  rw [cmHarrisGeometricGaloisDerivedAction_map_hom D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f]
  have hn := (EtaleDerivedSectionsPlus.homologyZeroIso
    ((geometricSchemes).obj U) Rcoeff).hom.naturality ((geometricSystem).map f)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- Canonical homology recovery is Galois-equivariant and natural in
the original coefficient reductions. -/
def cmHarrisGeometricGaloisDerivedHomologyIso (degree : ℕ) :
    derivedAction ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) degree).mapAction Galois ≅
      (cohomologyAction) degree :=
  (galoisCoefficients).derivedActionHomologyIso degree

/-- The equivariant homology comparison is exactly the canonical
comparison for the original geometric coefficient sheaf. -/
@[simp] theorem cmHarrisGeometricGaloisDerivedHomologyIso_hom_app_hom
    (degree : ℕ) (r : ℕᵒᵖ) :
    ((cmHarrisGeometricGaloisDerivedHomologyIso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid degree).hom.app r).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso
        ((geometricSchemes).obj U) Rcoeff degree).hom.app
          ((geometricSystem).obj r) := rfl

/-- Canonical degree-zero homology recovers the actual section system
with its Galois action and original reductions. -/
def cmHarrisGeometricGaloisDerivedZeroIso :
    derivedAction ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat Rcoeff) 0).mapAction Galois ≅
      sectionsAction :=
  (galoisCoefficients).derivedActionZeroIso

/-- The equivariant degree-zero comparison is exactly the canonical
map to the actual sections of the original geometric coefficient sheaf. -/
@[simp] theorem cmHarrisGeometricGaloisDerivedZeroIso_hom_app_hom
    (r : ℕᵒᵖ) :
    ((cmHarrisGeometricGaloisDerivedZeroIso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid).hom.app r).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso
        ((geometricSchemes).obj U) Rcoeff).hom.app
          ((geometricSystem).obj r) := rfl

/-- Ordinary degree-zero cohomology recovers actual global sections,
equivariantly and compatibly with every original coefficient reduction. -/
def cmHarrisGeometricGaloisCohomologyZeroIso :
    (cohomologyAction) 0 ≅ sectionsAction :=
  ((galoisCoefficients).derivedActionHomologyIso 0).symm ≪≫
    (galoisCoefficients).derivedActionZeroIso

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
