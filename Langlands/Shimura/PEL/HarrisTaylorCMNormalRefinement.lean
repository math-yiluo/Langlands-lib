import Langlands.Shimura.PEL.HarrisTaylorCMNormalActions
import Langlands.Shimura.NormalLevelCover
import Langlands.Shimura.EquivariantFormsHecke

/-! # Finite residual groups and equivariant refinements of actual CM schemes -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura

namespace PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)


section ResidualGroups

/-- The residual quotient is the quotient of the actual original level groups. -/
abbrev SmallCMResidualGroup (U V : SmallCMLevel D) :=
  U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup

omit [IsCMField F] [IsScalarTower E F A] in
/-- Compactness of the coarse level and openness of the fine level give finiteness. -/
theorem smallCMResidualGroup_finite (U V : SmallCMLevel D) :
    Finite (SmallCMResidualGroup D U V) := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  exact inferInstanceAs
    (Finite (U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup))

variable (U V W : SmallCMLevel D)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  [(W.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Specialize the existing normal-quotient homomorphism to the actual CM levels. -/
def smallCMResidualQuotientMap (hWV : W.obj.subgroup ≤ V.obj.subgroup) :
    SmallCMResidualGroup D U W →* SmallCMResidualGroup D U V :=
  LevelSpace.normalQuotientMap U.obj.subgroup
    (W.obj.subgroup.subgroupOf U.obj.subgroup) (fun _ hx => hWV hx)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMResidualQuotientMap_mk
    (hWV : W.obj.subgroup ≤ V.obj.subgroup) (g : U.obj.subgroup) :
    smallCMResidualQuotientMap D U V W hWV (QuotientGroup.mk g) =
      QuotientGroup.mk g := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Every coarse residual element has an actual fine residual lift. -/
theorem smallCMResidualQuotientMap_surjective
    (hWV : W.obj.subgroup ≤ V.obj.subgroup) :
    Function.Surjective (smallCMResidualQuotientMap D U V W hWV) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H g => exact ⟨QuotientGroup.mk g, rfl⟩

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMResidualQuotientMap_refl :
    smallCMResidualQuotientMap D U V V (le_refl _) =
      MonoidHom.id (SmallCMResidualGroup D U V) := by
  exact LevelSpace.normalQuotientMap_refl U.obj.subgroup
    (V.obj.subgroup.subgroupOf U.obj.subgroup)

variable (Z : SmallCMLevel D)
  [(Z.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Successive residual homomorphisms equal the map of the composite inclusion. -/
@[simp] theorem smallCMResidualQuotientMap_comp
    (hWV : W.obj.subgroup ≤ V.obj.subgroup)
    (hZW : Z.obj.subgroup ≤ W.obj.subgroup) :
    (smallCMResidualQuotientMap D U V W hWV).comp
        (smallCMResidualQuotientMap D U W Z hZW) =
      smallCMResidualQuotientMap D U V Z (hZW.trans hWV) := by
  exact LevelSpace.normalQuotientMap_comp U.obj.subgroup
    (Z.obj.subgroup.subgroupOf U.obj.subgroup)
    (fun _ hx => hZW hx) (fun _ hx => hWV hx)

end ResidualGroups

section Transporters

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The actual identity-element inclusion agrees with the identity at one level. -/
@[simp] theorem smallCMInclusion_refl (V : SmallCMLevel D) :
    smallCMInclusion D (le_refl V.obj.subgroup) = 𝟙 V := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Actual identity-element inclusions compose as subgroup inclusions do. -/
@[reassoc] theorem smallCMInclusion_trans {U V W : SmallCMLevel D}
    (hWV : W.obj.subgroup ≤ V.obj.subgroup)
    (hVU : V.obj.subgroup ≤ U.obj.subgroup) :
    smallCMInclusion D hWV ≫ smallCMInclusion D hVU =
      smallCMInclusion D (hWV.trans hVU) := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  exact one_mul 1

variable (U V W : SmallCMLevel D)
  (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  (hWV : W.obj.subgroup ≤ V.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  [(W.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Inverse right translation commutes with the actual finer-level inclusion. -/
theorem smallCMNormalInverseArrow_inclusion (g : U.obj.subgroup) :
    smallCMNormalInverseArrow D U W (hWV.trans hVU) g ≫ smallCMInclusion D hWV =
      smallCMInclusion D hWV ≫ smallCMNormalInverseArrow D U V hVU g := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  exact (mul_one _).trans (one_mul _).symm

end Transporters

variable {L : Type} [Field L] [NumberField L] [IsCMField L]
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

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V W : SmallCMLevel D)
  (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  (hWV : W.obj.subgroup ≤ V.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  [(W.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Actual scheme forgetting is equivariant for the proved residual homomorphism. -/
def representedCMNormalRefinement :
    quotientAction R U W (hWV.trans hVU) ⟶
      (Action.res Scheme (smallCMResidualQuotientMap D U V W hWV)).obj
        (quotientAction R U V hVU) where
  hom := (schemes R).map (smallCMInclusion D hWV)
  comm g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (schemes R).map (smallCMNormalInverseArrow D U W (hWV.trans hVU) g) ≫
          (schemes R).map (smallCMInclusion D hWV) =
        (schemes R).map (smallCMInclusion D hWV) ≫
          (schemes R).map (smallCMNormalInverseArrow D U V hVU g)
      rw [← (schemes R).map_comp, ← (schemes R).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "refinement" => representedCMNormalRefinement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[simp] theorem representedCMNormalRefinement_hom :
    (refinement R U V W hVU hWV).hom =
      (schemes R).map (smallCMInclusion D hWV) := rfl

/-- The equivariant refinement is an actual morphism over the original CM field. -/
theorem representedCMNormalRefinement_over :
    (refinement R U V W hVU hWV).hom ≫ (R V).base.obj.hom = (R W).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor R (smallCMInclusion D hWV)

/-- Its actual admissible-test interpretation is exactly the original level forgetting. -/
theorem representedCMNormalRefinement_classes
    (S : ComponentwiseAdmissibleCMBaseCategory D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality)
    (f : S ⟶ (R W).base) :
    (R V).represents.hom.app (Opposite.op S)
        (ULift.up (f ≫ (representedCMBaseTower D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor R).map (smallCMInclusion D hWV))) =
      ((moduli).map (smallCMInclusion D hWV)).app (Opposite.op S)
        ((R W).represents.hom.app (Opposite.op S) (ULift.up f)) :=
  representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMInclusion D hWV) S f

/-- Refining by the identity gives the identity actual scheme map. -/
@[simp] theorem representedCMNormalRefinement_refl :
    (refinement R U V V hVU (le_refl _)).hom = 𝟙 ((schemes R).obj V) := by
  change (schemes R).map (smallCMInclusion D (le_refl _)) = _
  rw [smallCMInclusion_refl, (schemes R).map_id]

/-- The refinement respects the invariant projection to the original coarse level. -/
@[reassoc] theorem representedCMNormalRefinement_projection :
    (refinement R U V W hVU hWV).hom ≫ projection R U V hVU =
      projection R U W (hWV.trans hVU) := by
  change (schemes R).map (smallCMInclusion D hWV) ≫
      (schemes R).map (smallCMInclusion D hVU) =
    (schemes R).map (smallCMInclusion D (hWV.trans hVU))
  rw [← (schemes R).map_comp, smallCMInclusion_trans]

variable (Z : SmallCMLevel D)
  [(Z.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Successive actual equivariant refinements compose to the direct forgetting map. -/
@[reassoc] theorem representedCMNormalRefinement_comp
    (hZW : Z.obj.subgroup ≤ W.obj.subgroup) :
    (refinement R U W Z (hWV.trans hVU) hZW).hom ≫
        (refinement R U V W hVU hWV).hom =
      (refinement R U V Z hVU (hZW.trans hWV)).hom := by
  change (schemes R).map (smallCMInclusion D hZW) ≫
      (schemes R).map (smallCMInclusion D hWV) =
    (schemes R).map (smallCMInclusion D (hZW.trans hWV))
  rw [← (schemes R).map_comp, smallCMInclusion_trans]

variable (R' : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "compareReps" => representedCMSchemeTowerComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R R'

/-- The same canonical comparisons identifying the quotient actions respect refinement. -/
theorem representedCMNormalRefinement_comparison :
    (compareReps).hom.app W ≫ (refinement R' U V W hVU hWV).hom =
      (refinement R U V W hVU hWV).hom ≫ (compareReps).hom.app V :=
  ((compareReps).hom.naturality (smallCMInclusion D hWV)).symm

/-- Actual normal-level equivariant refinement conditional on exactly the existence target. -/
def cmNormalRefinement
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) :=
  refinement (chosenCMLevelRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q) U V W hVU hWV

end PEL.HarrisTaylorCMWeilLevel
end Langlands.Shimura
