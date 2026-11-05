import Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalActions
import Langlands.Shimura.Coefficients.EtaleTorsorPullback

/-! # Finite geometric torsors on the exact geometric CM levels -/

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

local notation "geometricAction" => cmGeometricNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU

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
local notation "normalSquare" => cmGeometricSchemeTower_map_isPullback D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q (smallCMInclusion D hVU)
local notation "originalTorsor" => cmNormalGeometricTorsor_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  U V hVU q existence geometry hRigid criterion
local notation "originalMap" => (schemes).map (smallCMInclusion D hVU)

/-- Regard the original geometric action as an action in the exact coarse
level's small-etale category. -/
def cmGeometricNormalEtaleAction_of_dominantCriterion :
    Action ((geometricSchemes).obj U).Etale ResidualGroup := by
  let : Etale geometricMap := (geometricCover).property.2
  exact
    { V := Scheme.Etale.mk geometricMap
      ρ :=
        { toFun := fun g => MorphismProperty.Over.homMk ((geometricAction).ρ g)
            (cmGeometricNormalProjection_invariant D C preservation composition
              unitCoherence associativity comparison symmetry stability square universality
              dualityNaturality polarizationStability compatibility h htor q U V hVU g)
          map_one' := by
            apply MorphismProperty.Over.Hom.ext
            exact (geometricAction).ρ.map_one
          map_mul' := fun g g' => by
            apply MorphismProperty.Over.Hom.ext
            exact (geometricAction).ρ.map_mul g g' } }

local notation "etaleAction" => cmGeometricNormalEtaleAction_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

@[simp] theorem cmGeometricNormalEtaleAction_of_dominantCriterion_left :
    (etaleAction).V.left = (geometricSchemes).obj V := rfl

@[simp] theorem cmGeometricNormalEtaleAction_of_dominantCriterion_hom :
    (etaleAction).V.hom = geometricMap := rfl

@[simp] theorem cmGeometricNormalEtaleAction_of_dominantCriterion_ρ_left
    (g : ResidualGroup) :
    ((etaleAction).ρ g).left = (geometricAction).ρ g := rfl

local notation "pulledAction" =>
  (etaleTorsorPullbackFunctor ((projection).app U) ResidualGroup).obj
    (originalTorsor).val

/-- The canonical cartesian comparison identifies the exact geometric
small-etale action with the generic pullback of the original torsor. -/
def cmGeometricNormalEtaleActionPullbackIso : etaleAction ≅ pulledAction :=
  Action.mkIso
    (MorphismProperty.Over.isoMk (normalSquare).isoPullback
      (normalSquare).isoPullback_hom_snd) (by
    intro g
    apply MorphismProperty.Over.Hom.ext
    change (geometricAction).ρ g ≫ (normalSquare).isoPullback.hom =
      (normalSquare).isoPullback.hom ≫ ((pulledAction).ρ g).left
    have hf :
        ((pulledAction).ρ g).left ≫ pullback.fst originalMap ((projection).app U) =
          pullback.fst originalMap ((projection).app U) ≫ (originalAction).ρ g :=
      etaleTorsorPullbackFunctor_ρ_fst ((projection).app U) (originalTorsor).val g
    have hs :
        ((pulledAction).ρ g).left ≫ pullback.snd originalMap ((projection).app U) =
          pullback.snd originalMap ((projection).app U) :=
      etaleTorsorPullbackFunctor_ρ_snd ((projection).app U) (originalTorsor).val g
    apply pullback.hom_ext
    · rw [Category.assoc, (normalSquare).isoPullback_hom_fst,
        Category.assoc, hf, ← Category.assoc, (normalSquare).isoPullback_hom_fst]
      exact cmGeometricNormalQuotientAction_projection D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U V hVU g
    · rw [Category.assoc, (normalSquare).isoPullback_hom_snd,
        Category.assoc, hs, (normalSquare).isoPullback_hom_snd]
      exact cmGeometricNormalProjection_invariant D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U V hVU g)

local notation "etaleIso" => cmGeometricNormalEtaleActionPullbackIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

/-- The equivariant comparison uses the original canonical cartesian isomorphism. -/
@[simp] theorem cmGeometricNormalEtaleActionPullbackIso_hom_left :
    (etaleIso).hom.hom.left = (normalSquare).isoPullback.hom := rfl

@[simp] theorem cmGeometricNormalEtaleActionPullbackIso_inv_left :
    (etaleIso).inv.hom.left = (normalSquare).isoPullback.inv := rfl

/-- Transfer the generic pulled-back torsor condition to the exact existing
geometric CM level by the constructed equivariant comparison. -/
theorem cmGeometricNormalEtaleAction_isFiniteGeometricTorsor_of_dominantCriterion :
    IsFiniteGeometricTorsor ((geometricSchemes).obj U) etaleAction := by
  have hp := (originalTorsor).property.pullback ((projection).app U) (originalTorsor).val
  let : IsFinite geometricMap := (geometricCover).property.1
  let : Surjective originalMap := ⟨(originalTorsor).property.2.2.1⟩
  let : Surjective geometricMap :=
    MorphismProperty.of_isPullback (P := @Surjective) normalSquare inferInstance
  have hi : IsIso (etaleIso).hom.hom.left := by
    change IsIso (normalSquare).isoPullback.hom
    infer_instance
  have hc (g : ResidualGroup) :
      ((etaleAction).ρ g).left ≫ (etaleIso).hom.hom.left =
        (etaleIso).hom.hom.left ≫ ((pulledAction).ρ g).left :=
    congrArg (fun k => k.left) ((etaleIso).hom.comm g)
  have hw : (etaleIso).hom.hom.left ≫ (pulledAction).V.hom = geometricMap :=
    MorphismProperty.Over.w (etaleIso).hom.hom
  refine ⟨hp.1, inferInstanceAs (IsFinite geometricMap), (geometricMap).surjective, ?_⟩
  intro Ω _ _ a b hab
  change a ≫ geometricMap = b ≫ geometricMap at hab
  obtain ⟨g, hg, hu⟩ := hp.2.2.2 Ω
    (a ≫ (etaleIso).hom.hom.left) (b ≫ (etaleIso).hom.hom.left)
    (by simpa only [Category.assoc, hw] using hab)
  refine ⟨g, ?_, ?_⟩
  · apply (cancel_mono (etaleIso).hom.hom.left).mp
    simpa only [Category.assoc, hc g] using hg
  · intro g' hg'
    apply hu g'
    simpa only [Category.assoc, hc g'] using
      congrArg (fun k => k ≫ (etaleIso).hom.hom.left) hg'

/-- The exact geometric CM action together with its proved finite geometric
torsor condition, under the original named prerequisites. -/
def cmGeometricNormalGeometricTorsor_of_dominantCriterion :
    {Y : Action ((geometricSchemes).obj U).Etale ResidualGroup //
      IsFiniteGeometricTorsor ((geometricSchemes).obj U) Y} :=
  ⟨etaleAction,
    cmGeometricNormalEtaleAction_isFiniteGeometricTorsor_of_dominantCriterion D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor
      q U V hVU existence geometry hRigid criterion⟩

local notation "geometricTorsor" => cmGeometricNormalGeometricTorsor_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

@[simp] theorem cmGeometricNormalGeometricTorsor_of_dominantCriterion_val :
    (geometricTorsor).val = etaleAction := rfl

@[simp] theorem cmGeometricNormalGeometricTorsor_of_dominantCriterion_left :
    (geometricTorsor).val.V.left = (geometricSchemes).obj V := rfl

@[simp] theorem cmGeometricNormalGeometricTorsor_of_dominantCriterion_hom :
    (geometricTorsor).val.V.hom = geometricMap := rfl

@[simp] theorem cmGeometricNormalGeometricTorsor_of_dominantCriterion_ρ_left
    (g : ResidualGroup) :
    ((geometricTorsor).val.ρ g).left = (geometricAction).ρ g := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
