import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients
import Mathlib.CategoryTheory.Endomorphism

/-! # Algebraic-closure automorphisms of the geometric CM scheme tower -/

noncomputable section

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
open Langlands.Shimura.Coefficients Langlands.Cohomology
open Langlands.Geometry

/-- Spectrum of an actual F-automorphism of the algebraic closure. -/
def cmGeometricGaloisBaseMap {F : Type} [Field F]
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    Spec (.of (AlgebraicClosure F)) ⟶ Spec (.of (AlgebraicClosure F)) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

/-- The algebraic-closure automorphism fixes the original field map. -/
@[reassoc (attr := simp)] theorem cmGeometricGaloisBaseMap_over {F : Type} [Field F]
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    cmGeometricGaloisBaseMap σ ≫ cmGeometricFieldMap (F := F) =
      cmGeometricFieldMap (F := F) := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact σ.toAlgHom.comp_algebraMap

@[simp] theorem cmGeometricGaloisBaseMap_one {F : Type} [Field F] :
    cmGeometricGaloisBaseMap (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) = 𝟙 _ := by
  change Spec.map (𝟙 (CommRingCat.of (AlgebraicClosure F))) = _
  exact Spec.map_id _

/-- The raw spectrum maps compose in the geometric, contravariant order. -/
theorem cmGeometricGaloisBaseMap_mul {F : Type} [Field F]
    (σ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    cmGeometricGaloisBaseMap (σ * τ) =
      cmGeometricGaloisBaseMap σ ≫ cmGeometricGaloisBaseMap τ := by
  unfold cmGeometricGaloisBaseMap
  rw [← Spec.map_comp]
  rfl

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

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "overTower" => representedCMOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor chosen
local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "geometricOver" => cmGeometricOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "projection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The actual fiber-product map fixing the original level and acting on its field factor. -/
def cmGeometricGaloisMap (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    geometricSchemes ⟶ geometricSchemes where
  app U := pullback.lift
    (pullback.fst ((overTower).obj U).hom (cmGeometricFieldMap (F := F)))
    (pullback.snd ((overTower).obj U).hom (cmGeometricFieldMap (F := F)) ≫
      cmGeometricGaloisBaseMap σ)
    (by rw [Category.assoc, cmGeometricGaloisBaseMap_over]; exact pullback.condition)
  naturality {U V} k := by
    apply pullback.hom_ext <;>
      simp [cmGeometricSchemeTower, cmGeometricOverTower]

local notation "galoisMap" => cmGeometricGaloisMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- These automorphisms fix the projection to the original represented level. -/
@[reassoc (attr := simp)] theorem cmGeometricGaloisMap_app_projection
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (U : SmallCMLevel D) :
    (galoisMap σ).app U ≫ (projection).app U = (projection).app U :=
  pullback.lift_fst _ _ _

/-- Their field-factor projection is precisely the specified spectrum map. -/
@[reassoc (attr := simp)] theorem cmGeometricGaloisMap_app_structure
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (U : SmallCMLevel D) :
    (galoisMap σ).app U ≫ ((geometricOver).obj U).hom =
      ((geometricOver).obj U).hom ≫ cmGeometricGaloisBaseMap σ :=
  pullback.lift_snd _ _ _

@[simp] theorem cmGeometricGaloisMap_one : galoisMap 1 = 𝟙 _ := by
  ext U
  apply pullback.hom_ext <;> simp [cmGeometricGaloisMap]
  all_goals exact Category.id_comp _

/-- Composition retains the raw contravariant spectrum convention at every level. -/
theorem cmGeometricGaloisMap_mul
    (σ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    galoisMap (σ * τ) = galoisMap σ ≫ galoisMap τ := by
  ext U
  apply pullback.hom_ext <;>
    simp [cmGeometricGaloisMap, cmGeometricGaloisBaseMap_mul]

/-- The inverse field automorphism gives the inverse natural fiber-product map. -/
def cmGeometricGaloisIso (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    geometricSchemes ≅ geometricSchemes where
  hom := galoisMap σ
  inv := galoisMap σ⁻¹
  hom_inv_id := by rw [← cmGeometricGaloisMap_mul, mul_inv_cancel,
    cmGeometricGaloisMap_one]
  inv_hom_id := by rw [← cmGeometricGaloisMap_mul, inv_mul_cancel,
    cmGeometricGaloisMap_one]

local notation "galoisIso" => cmGeometricGaloisIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- Inverse comorphisms turn the raw right action into a left action on the whole tower. -/
def cmGeometricGaloisAction :
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →* Aut geometricSchemes where
  toFun σ := galoisIso σ⁻¹
  map_one' := by
    apply Iso.ext
    exact cmGeometricGaloisMap_one D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q
  map_mul' σ τ := by
    apply Iso.ext
    change galoisMap ((σ * τ)⁻¹) = galoisMap τ⁻¹ ≫ galoisMap σ⁻¹
    rw [mul_inv_rev, cmGeometricGaloisMap_mul]

local notation "galoisAction" => cmGeometricGaloisAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The left action has the explicit inverse-comorphism normalization. -/
@[simp] theorem cmGeometricGaloisAction_hom
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    ((galoisAction) σ).hom = galoisMap σ⁻¹ := rfl

/-- Evaluation gives an actual automorphism action on each geometric CM scheme. -/
def cmGeometricGaloisLevelAction (U : SmallCMLevel D) :
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →*
      Aut ((geometricSchemes).obj U) :=
  (Functor.mapAut geometricSchemes
    ((evaluation (SmallCMLevel D) Scheme).obj U)).comp galoisAction

/-- Every original level map intertwines the constructed left action. -/
theorem cmGeometricGaloisAction_naturality
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    {U V : SmallCMLevel D} (k : U ⟶ V) :
    (geometricSchemes).map k ≫ ((galoisAction) σ).hom.app V =
      ((galoisAction) σ).hom.app U ≫ (geometricSchemes).map k :=
  ((galoisAction) σ).hom.naturality k

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
