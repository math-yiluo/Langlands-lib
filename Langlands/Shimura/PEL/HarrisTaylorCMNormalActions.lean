import Langlands.Shimura.PEL.HarrisTaylorCMLevelCosets
import Langlands.Shimura.PEL.HarrisTaylorCMHeckeSchemes
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Actual normal-level quotient actions on represented CM schemes -/

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

namespace CompactOpenLevel

variable {G : Type u} [Group G] [TopologicalSpace G]
  (U V : CompactOpenLevel G) (hVU : V.subgroup ≤ U.subgroup)
  [(V.subgroup.subgroupOf U.subgroup).Normal]

/-- Relative normality gives the genuine transporter for inverse right translation. -/
def normalInverseArrow (g : U.subgroup) : V ⟶ V where
  element := (g : G)⁻¹
  respects k hk := by
    have hk' : (⟨k, hVU hk⟩ : U.subgroup) ∈ V.subgroup.subgroupOf U.subgroup := hk
    have e := (inferInstance : (V.subgroup.subgroupOf U.subgroup).Normal).conj_mem
      (⟨k, hVU hk⟩ : U.subgroup) hk' g
    have e' : (g : G) * k * (g : G)⁻¹ ∈ V.subgroup := e
    simpa using e'

@[simp] theorem normalInverseArrow_element (g : U.subgroup) :
    (normalInverseArrow U V hVU g).element = (g : G)⁻¹ := rfl

@[simp] theorem normalInverseArrow_one :
    normalInverseArrow U V hVU 1 = 𝟙 V := by
  apply Arrow.ext
  simp [normalInverseArrow]

/-- Inversion reverses transporter composition, as required for a left action. -/
theorem normalInverseArrow_mul (g k : U.subgroup) :
    normalInverseArrow U V hVU (g * k) =
      normalInverseArrow U V hVU k ≫ normalInverseArrow U V hVU g := by
  apply Arrow.ext
  simp [normalInverseArrow, mul_inv_rev]

end CompactOpenLevel

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

section Transporters

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Inverse right translation as an actual endomorphism of the small fine level. -/
def smallCMNormalInverseArrow (g : U.obj.subgroup) : V ⟶ V :=
  ObjectProperty.homMk (CompactOpenLevel.normalInverseArrow U.obj V.obj hVU g)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMNormalInverseArrow_element (g : U.obj.subgroup) :
    (smallCMNormalInverseArrow D U V hVU g).hom.element =
      (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹ := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMNormalInverseArrow_one :
    smallCMNormalInverseArrow D U V hVU 1 = 𝟙 V := by
  apply ObjectProperty.hom_ext
  exact CompactOpenLevel.normalInverseArrow_one U.obj V.obj hVU

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Multiplication in the original opposite group gives the left-action order. -/
theorem smallCMNormalInverseArrow_mul (g k : U.obj.subgroup) :
    smallCMNormalInverseArrow D U V hVU (g * k) =
      smallCMNormalInverseArrow D U V hVU k ≫
        smallCMNormalInverseArrow D U V hVU g := by
  apply ObjectProperty.hom_ext
  exact CompactOpenLevel.normalInverseArrow_mul U.obj V.obj hVU g k

/-- Any actual small-level tower carries the inverse-right action of the coarse level. -/
def smallCMNormalLevelAction {B : Type u} [Category.{v} B]
    (T : SmallCMLevel D ⥤ B) : Action B U.obj.subgroup where
  V := T.obj V
  ρ :=
    { toFun g := T.map (smallCMNormalInverseArrow D U V hVU g)
      map_one' := by
        change T.map (smallCMNormalInverseArrow D U V hVU 1) = 𝟙 _
        simp
      map_mul' g k := by
        rw [smallCMNormalInverseArrow_mul, T.map_comp]
        rfl }

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

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "ResidualGroup" =>
  U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup
local notation "levelAction" => smallCMNormalLevelAction D U V hVU (baseTower R)

/-- The fine subgroup lies in the kernel by the actual frame-orbit coset calculation. -/
theorem representedCMNormalBaseAction_kernel :
    V.obj.subgroup.subgroupOf U.obj.subgroup ≤ (levelAction).ρ.ker := by
  intro g hg
  change (baseTower R).map (smallCMNormalInverseArrow D U V hVU g) = 𝟙 _
  have hgid :
      (smallCMNormalInverseArrow D U V hVU g).hom.element⁻¹ *
        (𝟙 V : V ⟶ V).hom.element ∈ V.obj.subgroup := by
    have hg' : (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ∈
        V.obj.subgroup := hg
    simpa using hg'
  simpa using representedCMBaseTower_map_eq_of_target_coset D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R
    (smallCMNormalInverseArrow D U V hVU g) (𝟙 V) hgid

/-- The actual residual quotient acts on the exact represented admissible CM base. -/
def representedCMNormalQuotientBaseAction : Action DisBases ResidualGroup where
  V := (R V).base
  ρ := QuotientGroup.lift (V.obj.subgroup.subgroupOf U.obj.subgroup) (levelAction).ρ
    (representedCMNormalBaseAction_kernel D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU)

local notation "baseAction" => representedCMNormalQuotientBaseAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R U V hVU

@[simp] theorem representedCMNormalQuotientBaseAction_mk (g : U.obj.subgroup) :
    (baseAction).ρ (QuotientGroup.mk g) =
      (baseTower R).map (smallCMNormalInverseArrow D U V hVU g) := rfl

/-- Forgetting the actual quotient action gives an action by actual Scheme morphisms. -/
def representedCMNormalQuotientAction : Action Scheme ResidualGroup :=
  ((ObjectProperty.ι (ComponentwiseAdmissibleCMBase D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality) ⋙
    Over.forget (Spec (.of F))).mapAction ResidualGroup).obj (baseAction)

local notation "schemeAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R U V hVU

/-- A quotient representative acts by the original actual inverse-right transition. -/
@[simp] theorem representedCMNormalQuotientAction_mk (g : U.obj.subgroup) :
    (schemeAction).ρ (QuotientGroup.mk g) =
      (schemes R).map (smallCMNormalInverseArrow D U V hVU g) := rfl

/-- Every residual element gives an automorphism of the actual fine scheme. -/
def representedCMNormalQuotientAutomorphism (g : ResidualGroup) :
    Aut ((schemes R).obj V) :=
  (schemeAction).ρAut g

@[simp] theorem representedCMNormalQuotientAutomorphism_hom (g : ResidualGroup) :
    (representedCMNormalQuotientAutomorphism D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU g).hom = (schemeAction).ρ g := rfl

@[simp] theorem representedCMNormalQuotientAutomorphism_inv (g : ResidualGroup) :
    (representedCMNormalQuotientAutomorphism D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU g).inv =
        (schemeAction).ρ g⁻¹ := rfl

/-- The residual action is over the original CM field. -/
theorem representedCMNormalQuotientAction_over (g : ResidualGroup) :
    (schemeAction).ρ g ≫ (R V).base.obj.hom = (R V).base.obj.hom := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    exact representedCMSchemeTower_over D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R (smallCMNormalInverseArrow D U V hVU g)

/-- The residual action has the original class interpretation on every admissible test scheme. -/
theorem representedCMNormalQuotientBaseAction_mk_classes (g : U.obj.subgroup)
    (S : DisBases) (f : S ⟶ (R V).base) :
    (R V).represents.hom.app (Opposite.op S)
        (ULift.up (f ≫ (baseAction).ρ (QuotientGroup.mk g))) =
      ((moduli).map (smallCMNormalInverseArrow D U V hVU g)).app (Opposite.op S)
        ((R V).represents.hom.app (Opposite.op S) (ULift.up f)) :=
  representedCMBaseTower_map_classes D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R (smallCMNormalInverseArrow D U V hVU g) S f

/-- The actual forgetting map to the coarse scheme. -/
def representedCMNormalProjection : (schemes R).obj V ⟶ (schemes R).obj U :=
  (schemes R).map (smallCMInclusion D hVU)

local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R U V hVU

/-- The quotient action preserves forgetting, by equality of actual coarse target cosets. -/
@[reassoc] theorem representedCMNormalProjection_invariant (g : ResidualGroup) :
    (schemeAction).ρ g ≫ projection = projection := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    change (schemes R).map (smallCMNormalInverseArrow D U V hVU g) ≫
        (schemes R).map (smallCMInclusion D hVU) =
      (schemes R).map (smallCMInclusion D hVU)
    rw [← (schemes R).map_comp]
    apply representedCMSchemeTower_map_eq_of_target_coset D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R
    change (((g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹ * 1)⁻¹ * 1) ∈
      U.obj.subgroup
    simp

/-- Forgetting is a morphism to the trivial residual action on the coarse scheme. -/
def representedCMNormalQuotientProjection :
    schemeAction ⟶ Action.trivial ResidualGroup ((schemes R).obj U) where
  hom := projection
  comm g := by
    simpa using representedCMNormalProjection_invariant D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU g

variable (R' : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "compareReps" => representedCMSchemeTowerComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R R'

/-- Canonical changes of exact representations identify the actual quotient actions. -/
def representedCMNormalQuotientActionComparison :
    schemeAction ≅
      representedCMNormalQuotientAction D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R' U V hVU :=
  Action.mkIso ((compareReps).app V) (by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      exact (compareReps).hom.naturality (smallCMNormalInverseArrow D U V hVU g))

/-- The same canonical comparison also commutes with actual forgetting. -/
theorem representedCMNormalProjection_comparison :
    (representedCMNormalQuotientActionComparison D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor R U V hVU R').hom.hom ≫
      representedCMNormalProjection D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor R' U V hVU =
      projection ≫ (compareReps).hom.app U :=
  ((compareReps).hom.naturality (smallCMInclusion D hVU)).symm

/-- The actual normal-level quotient action from precisely the stated existence target. -/
def cmNormalQuotientAction
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) :
    Action Scheme ResidualGroup :=
  representedCMNormalQuotientAction D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor (chosenCMLevelRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q) U V hVU

end PEL.HarrisTaylorCMWeilLevel
end Langlands.Shimura
