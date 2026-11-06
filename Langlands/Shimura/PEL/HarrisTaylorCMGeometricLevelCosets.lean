import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients
import Langlands.Shimura.PEL.HarrisTaylorCMLevelCosets

/-! # Target-coset maps on the actual geometric CM tower -/

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

/-- Target-coset equality is preserved by the actual change of base to Fbar. -/
theorem cmGeometricOverTower_map_eq_of_target_coset
    {U V : SmallCMLevel D} (f g : U ⟶ V)
    (hfg : f.hom.element⁻¹ * g.hom.element ∈ V.obj.subgroup) :
    (geometricOver).map f = (geometricOver).map g := by
  have heq : (overTower).map f = (overTower).map g := by
    apply (Over.forget (Spec (.of F))).map_injective
    exact representedCMSchemeTower_map_eq_of_target_coset D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor chosen f g hfg
  change (Over.pullback (cmGeometricFieldMap (F := F))).map ((overTower).map f) =
    (Over.pullback (cmGeometricFieldMap (F := F))).map ((overTower).map g)
  exact congrArg (fun a => (Over.pullback (cmGeometricFieldMap (F := F))).map a) heq

/-- Equal target cosets give exactly equal geometric scheme transitions. -/
theorem cmGeometricSchemeTower_map_eq_of_target_coset
    {U V : SmallCMLevel D} (f g : U ⟶ V)
    (hfg : f.hom.element⁻¹ * g.hom.element ∈ V.obj.subgroup) :
    (geometricSchemes).map f = (geometricSchemes).map g :=
  congrArg (fun a => a.left)
    (cmGeometricOverTower_map_eq_of_target_coset D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q f g hfg)

/-- The original transporter target-coset quotient acts by actual geometric maps. -/
def cmGeometricTargetCosetMap {U V : SmallCMLevel D} :
    SmallCMTargetCosetArrow D U V →
      ((geometricSchemes).obj U ⟶ (geometricSchemes).obj V) :=
  Quotient.lift (fun f => (geometricSchemes).map f) (fun f g hfg =>
    cmGeometricSchemeTower_map_eq_of_target_coset D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q f g hfg)

local notation "cosetMap" => cmGeometricTargetCosetMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "originalCosetMap" => representedCMTargetCosetMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor chosen

/-- A representative recovers the unchanged geometric transporter map. -/
@[simp] theorem cmGeometricTargetCosetMap_mk {U V : SmallCMLevel D} (f : U ⟶ V) :
    cosetMap (Quotient.mk _ f) = (geometricSchemes).map f := rfl

/-- Coset-induced geometric maps remain over the original algebraic closure. -/
theorem cmGeometricTargetCosetMap_over {U V : SmallCMLevel D}
    (c : SmallCMTargetCosetArrow D U V) :
    cosetMap c ≫ ((geometricOver).obj V).hom = ((geometricOver).obj U).hom := by
  induction c using Quotient.inductionOn with
  | h f => exact Over.w ((geometricOver).map f)

/-- The geometric target-coset map is over its original chosen target-coset map. -/
@[reassoc] theorem cmGeometricTargetCosetMap_projection {U V : SmallCMLevel D}
    (c : SmallCMTargetCosetArrow D U V) :
    cosetMap c ≫ (projection).app V =
      (projection).app U ≫ originalCosetMap c := by
  induction c using Quotient.inductionOn with
  | h f => exact (projection).naturality f

/-- An actual element of a small level acts trivially on its geometric scheme. -/
theorem cmGeometricSchemeTower_map_eq_id_of_mem {U : SmallCMLevel D}
    (f : U ⟶ U) (hf : f.hom.element ∈ U.obj.subgroup) :
    (geometricSchemes).map f = 𝟙 _ := by
  have hfid : f.hom.element⁻¹ * (𝟙 U : U ⟶ U).hom.element ∈ U.obj.subgroup := by
    simpa using U.obj.subgroup.inv_mem hf
  simpa using cmGeometricSchemeTower_map_eq_of_target_coset D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q f (𝟙 U) hfid

/-- The identity transporter class is the identity on the actual geometric level. -/
@[simp] theorem cmGeometricTargetCosetMap_id (U : SmallCMLevel D) :
    cosetMap (Quotient.mk _ (𝟙 U)) = 𝟙 _ := by
  simp

/-- Composing actual representative maps agrees with the original transporter composition. -/
theorem cmGeometricTargetCosetMap_comp {U V W : SmallCMLevel D}
    (f : U ⟶ V) (g : V ⟶ W) :
    cosetMap (Quotient.mk _ f) ≫ cosetMap (Quotient.mk _ g) =
      cosetMap (Quotient.mk _ (f ≫ g)) :=
  ((geometricSchemes).map_comp f g).symm

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
