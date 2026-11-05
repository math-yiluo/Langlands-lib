import Langlands.Shimura.PEL.HarrisTaylorCMGeometricFiniteEtale
import Langlands.Shimura.PEL.HarrisTaylorCMNormalSmoothTorsor

/-! # Original residual actions on the actual geometric CM levels -/

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

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "ResidualGroup" => SmallCMResidualGroup D U V
local notation "baseAction" => representedCMNormalQuotientBaseAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor chosen U V hVU
local notation "originalAction" => cmNormalQuotientAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q
local notation "geometricMap" => (geometricSchemes).map (smallCMInclusion D hVU)

/-- The original residual action, base changed to the algebraic closure of F. -/
def cmGeometricNormalQuotientOverAction :
    Action (Over (Spec (.of (AlgebraicClosure F)))) ResidualGroup :=
  ((ObjectProperty.ι (ComponentwiseAdmissibleCMBase D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality) ⋙
    Over.pullback (cmGeometricFieldMap (F := F))).mapAction ResidualGroup).obj baseAction

local notation "overAction" => cmGeometricNormalQuotientOverAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU

/-- The action uses the existing geometric fine level over the original geometric field. -/
@[simp] theorem cmGeometricNormalQuotientOverAction_V :
    (overAction).V = (geometricOver).obj V := rfl

/-- Forget only the field structure from the same constructed action. -/
def cmGeometricNormalQuotientAction : Action Scheme ResidualGroup :=
  ((Over.forget (Spec (.of (AlgebraicClosure F)))).mapAction ResidualGroup).obj overAction

local notation "geometricAction" => cmGeometricNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU

@[simp] theorem cmGeometricNormalQuotientAction_V :
    (geometricAction).V = (geometricSchemes).obj V := rfl

/-- A representative acts by the original inverse-right geometric tower map. -/
@[simp] theorem cmGeometricNormalQuotientAction_mk (g : U.obj.subgroup) :
    (geometricAction).ρ (QuotientGroup.mk g) =
      (geometricSchemes).map (smallCMNormalInverseArrow D U V hVU g) := rfl

/-- The first fiber projection is equivariant for every original residual element. -/
@[reassoc (attr := simp)] theorem cmGeometricNormalQuotientAction_projection
    (g : ResidualGroup) :
    (geometricAction).ρ g ≫ (projection).app V =
      (projection).app V ≫ (originalAction).ρ g := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    exact (projection).naturality (smallCMNormalInverseArrow D U V hVU g)

/-- The action fixes the actual structure map to the algebraically closed field. -/
@[reassoc (attr := simp)] theorem cmGeometricNormalQuotientAction_over
    (g : ResidualGroup) :
    (geometricAction).ρ g ≫ ((geometricOver).obj V).hom =
      ((geometricOver).obj V).hom :=
  Over.w ((overAction).ρ g)

/-- Original forgetting invariance survives the actual field-base-change functor. -/
@[reassoc (attr := simp)] theorem cmGeometricNormalProjection_invariant
    (g : ResidualGroup) :
    (geometricAction).ρ g ≫ geometricMap = geometricMap := by
  have ho :
      ((ObjectProperty.ι (ComponentwiseAdmissibleCMBase D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality)).map
          ((baseAction).ρ g)) ≫ (overTower).map (smallCMInclusion D hVU) =
        (overTower).map (smallCMInclusion D hVU) := by
    apply Over.OverMorphism.ext
    exact representedCMNormalProjection_invariant D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor chosen U V hVU g
  change ((Over.pullback (cmGeometricFieldMap (F := F))).map
    ((ObjectProperty.ι (ComponentwiseAdmissibleCMBase D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality)).map
        ((baseAction).ρ g))).left ≫
    ((Over.pullback (cmGeometricFieldMap (F := F))).map
      ((overTower).map (smallCMInclusion D hVU))).left =
    ((Over.pullback (cmGeometricFieldMap (F := F))).map
      ((overTower).map (smallCMInclusion D hVU))).left
  simpa only [Functor.map_comp, Over.comp_left] using
    congrArg (fun k => k.left)
      (congrArg (fun k => (Over.pullback (cmGeometricFieldMap (F := F))).map k) ho)

/-- The geometric projection to the original fine level is an action morphism. -/
def cmGeometricNormalQuotientProjection : geometricAction ⟶ originalAction where
  hom := (projection).app V
  comm g := (cmGeometricNormalQuotientAction_projection D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V hVU g)

/-- The actual geometric normal forgetting map is equivariant for the trivial action. -/
def cmGeometricNormalQuotientForgetting :
    geometricAction ⟶ Action.trivial ResidualGroup ((geometricSchemes).obj U) where
  hom := geometricMap
  comm g := by
    simpa using cmGeometricNormalProjection_invariant D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU g

open Langlands.AlgebraicGeometry.FiniteEtale

variable
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)
  (criterion : DominantUnramifiedEtaleStatement.{0})

local notation "geometricCover" => cmGeometricNormalFiniteEtale_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

local notation "originalFiniteAction" => cmNormalFiniteEtaleAction_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  U V hVU q existence geometry hRigid criterion

local notation "originalCover" => cmNormalFiniteEtale_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  U V hVU q existence geometry hRigid criterion

local notation "coverIso" => cmGeometricNormalFiniteEtalePullbackIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

/-- The same geometric residual action on the already constructed exact finite-etale cover. -/
def cmGeometricNormalFiniteEtaleAction_of_dominantCriterion :
    Action (Cover ((geometricSchemes).obj U)) ResidualGroup where
  V := geometricCover
  ρ :=
    { toFun := fun g => ObjectProperty.homMk (Over.homMk ((geometricAction).ρ g)
        (cmGeometricNormalProjection_invariant D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U V hVU g))
      map_one' := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact (geometricAction).ρ.map_one
      map_mul' := fun g g' => by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact (geometricAction).ρ.map_mul g g' }

local notation "finiteAction" => cmGeometricNormalFiniteEtaleAction_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

@[simp] theorem cmGeometricNormalFiniteEtaleAction_of_dominantCriterion_V :
    (finiteAction).V = geometricCover := rfl

@[simp] theorem cmGeometricNormalFiniteEtaleAction_of_dominantCriterion_left :
    (finiteAction).V.obj.left = (geometricSchemes).obj V := rfl

@[simp] theorem cmGeometricNormalFiniteEtaleAction_of_dominantCriterion_hom :
    (finiteAction).V.obj.hom = geometricMap := rfl

@[simp] theorem cmGeometricNormalFiniteEtaleAction_of_dominantCriterion_ρ_left
    (g : ResidualGroup) :
    ((finiteAction).ρ g).hom.left = (geometricAction).ρ g := rfl

/-- The published canonical cover comparison is equivariant for the original residual group. -/
def cmGeometricNormalFiniteEtaleActionPullbackIso :
    finiteAction ≅
      ((pullbackFunctor ((projection).app U)).mapAction ResidualGroup).obj
        originalFiniteAction :=
  Action.mkIso coverIso (by
    intro g
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change (geometricAction).ρ g ≫ (coverIso).hom.hom.left =
      (coverIso).hom.hom.left ≫
        ((pullbackFunctor ((projection).app U)).map ((originalFiniteAction).ρ g)).hom.left
    have hf :
        ((pullbackFunctor ((projection).app U)).map ((originalFiniteAction).ρ g)).hom.left ≫
          pullback.fst (originalCover).obj.hom ((projection).app U) =
        pullback.fst (originalCover).obj.hom ((projection).app U) ≫ (originalAction).ρ g :=
      pullbackFunctor_map_hom_left_fst ((projection).app U) ((originalFiniteAction).ρ g)
    have hs :
        ((pullbackFunctor ((projection).app U)).map ((originalFiniteAction).ρ g)).hom.left ≫
          pullback.snd (originalCover).obj.hom ((projection).app U) =
        pullback.snd (originalCover).obj.hom ((projection).app U) :=
      pullbackFunctor_map_hom_left_snd ((projection).app U) ((originalFiniteAction).ρ g)
    apply pullback.hom_ext
    · rw [Category.assoc, cmGeometricNormalFiniteEtalePullbackIso_hom_fst,
        Category.assoc, hf, ← Category.assoc,
        cmGeometricNormalFiniteEtalePullbackIso_hom_fst]
      exact cmGeometricNormalQuotientAction_projection D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U V hVU g
    · rw [Category.assoc, cmGeometricNormalFiniteEtalePullbackIso_hom_snd,
        Category.assoc, hs, cmGeometricNormalFiniteEtalePullbackIso_hom_snd]
      exact cmGeometricNormalProjection_invariant D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U V hVU g)

local notation "finiteIso" => cmGeometricNormalFiniteEtaleActionPullbackIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

/-- Forgetting equivariance recovers the identical published canonical cover comparison. -/
@[simp] theorem cmGeometricNormalFiniteEtaleActionPullbackIso_hom_hom :
    (finiteIso).hom.hom = (coverIso).hom := rfl

@[simp] theorem cmGeometricNormalFiniteEtaleActionPullbackIso_inv_hom :
    (finiteIso).inv.hom = (coverIso).inv := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
