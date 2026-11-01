import Langlands.Shimura.PEL.HarrisTaylorCMNormalRefinement
import Mathlib.AlgebraicGeometry.Limits

/-! # Residual-action comparison with actual CM forgetting kernel pairs -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

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
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Actual disjoint union of the fine scheme indexed by the actual residual quotient. -/
def representedCMNormalCopies : Scheme :=
  ∐ (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V)

local notation "copies" => representedCMNormalCopies D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The kernel pair of the actual original forgetting morphism. -/
def representedCMNormalKernelPair : Scheme :=
  pullback (projection R U V hVU) (projection R U V hVU)

local notation "kernelPair" => representedCMNormalKernelPair D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The graph of a residual translate lies in the actual forgetting kernel pair. -/
def representedCMNormalGraph (g : SmallCMResidualGroup D U V) :
    (schemes R).obj V ⟶ kernelPair R U V hVU :=
  pullback.lift (𝟙 _) ((quotientAction R U V hVU).ρ g) (by
    simpa using (representedCMNormalProjection_invariant D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU g).symm)

local notation "graph" => representedCMNormalGraph D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[reassoc (attr := simp)] theorem representedCMNormalGraph_fst
    (g : SmallCMResidualGroup D U V) :
    graph R U V hVU g ≫ pullback.fst _ _ = 𝟙 _ := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem representedCMNormalGraph_snd
    (g : SmallCMResidualGroup D U V) :
    graph R U V hVU g ≫ pullback.snd _ _ = (quotientAction R U V hVU).ρ g := by
  exact pullback.lift_snd _ _ _

/-- The identity residual translate gives the actual diagonal. -/
@[simp] theorem representedCMNormalGraph_one :
    graph R U V hVU 1 = pullback.lift (𝟙 _) (𝟙 _) (by simp) := by
  apply pullback.hom_ext
  · rw [representedCMNormalGraph_fst, pullback.lift_fst]
  · rw [representedCMNormalGraph_snd, pullback.lift_snd]
    exact (quotientAction R U V hVU).ρ.map_one

/-- The concrete normal-cover comparison, with no isomorphism assumption or conclusion. -/
def representedCMNormalKernelComparison :
    copies R U V ⟶ kernelPair R U V hVU :=
  Sigma.desc (graph R U V hVU)

local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Each summand of the comparison is exactly the constructed residual graph. -/
@[reassoc (attr := simp)] theorem representedCMNormalKernelComparison_ι
    (g : SmallCMResidualGroup D U V) :
    Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) g ≫
        kernelComparison R U V hVU = graph R U V hVU g :=
  Sigma.ι_comp_desc _ _

/-- The first projection forgets the residual index. -/
@[reassoc (attr := simp)] theorem representedCMNormalKernelComparison_fst :
    kernelComparison R U V hVU ≫ pullback.fst _ _ =
      Sigma.desc (fun _ : SmallCMResidualGroup D U V => 𝟙 ((schemes R).obj V)) := by
  apply Sigma.hom_ext
  intro g
  simp

/-- The second projection applies the original residual action. -/
@[reassoc (attr := simp)] theorem representedCMNormalKernelComparison_snd :
    kernelComparison R U V hVU ≫ pullback.snd _ _ =
      Sigma.desc (fun g : SmallCMResidualGroup D U V => (quotientAction R U V hVU).ρ g) := by
  apply Sigma.hom_ext
  intro g
  rw [representedCMNormalKernelComparison_ι_assoc, representedCMNormalGraph_snd]
  exact (Sigma.ι_comp_desc
    (fun g : SmallCMResidualGroup D U V => (quotientAction R U V hVU).ρ g) g).symm

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
/-- Both kernel-pair projections have the same composite with original forgetting. -/
theorem representedCMNormalKernelPair_condition :
    pullback.fst (projection R U V hVU) (projection R U V hVU) ≫
        projection R U V hVU =
      pullback.snd (projection R U V hVU) (projection R U V hVU) ≫
        projection R U V hVU := pullback.condition

/-- The graph of a representative uses exactly the existing inverse-right transition. -/
@[reassoc] theorem representedCMNormalGraph_mk_snd (g : U.obj.subgroup) :
    graph R U V hVU (QuotientGroup.mk g) ≫ pullback.snd _ _ =
      (schemes R).map (smallCMNormalInverseArrow D U V hVU g) := by
  simp

section Refinement

variable (W : SmallCMLevel D) (hWV : W.obj.subgroup ≤ V.obj.subgroup)
  [(W.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "refinement" => representedCMNormalRefinement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "quotientMap" => smallCMResidualQuotientMap D U V W hWV

/-- Refinement on copies uses actual forgetting and the actual residual quotient map. -/
def representedCMNormalCopiesRefinement : copies R U W ⟶ copies R U V :=
  Sigma.desc (fun g : SmallCMResidualGroup D U W =>
    (refinement R U V W hVU hWV).hom ≫
      Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) (quotientMap g))

local notation "copiesRefinement" => representedCMNormalCopiesRefinement D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[reassoc (attr := simp)] theorem representedCMNormalCopiesRefinement_ι
    (g : SmallCMResidualGroup D U W) :
    Sigma.ι (fun _ : SmallCMResidualGroup D U W => (schemes R).obj W) g ≫
        copiesRefinement R U V hVU W hWV =
      (refinement R U V W hVU hWV).hom ≫
        Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) (quotientMap g) :=
  Sigma.ι_comp_desc _ _

/-- Actual forgetting in both factors induces refinement on its actual kernel pair. -/
def representedCMNormalKernelPairRefinement :
    kernelPair R U W (hWV.trans hVU) ⟶ kernelPair R U V hVU :=
  pullback.lift
    (pullback.fst _ _ ≫ (refinement R U V W hVU hWV).hom)
    (pullback.snd _ _ ≫ (refinement R U V W hVU hWV).hom) (by
      simp only [Category.assoc, representedCMNormalRefinement_projection]
      exact pullback.condition)

local notation "kernelRefinement" => representedCMNormalKernelPairRefinement D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[reassoc (attr := simp)] theorem representedCMNormalKernelPairRefinement_fst :
    kernelRefinement R U V hVU W hWV ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (refinement R U V W hVU hWV).hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem representedCMNormalKernelPairRefinement_snd :
    kernelRefinement R U V hVU W hWV ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (refinement R U V W hVU hWV).hom :=
  pullback.lift_snd _ _ _

/-- The graph square is forced by the proved equivariance of actual forgetting. -/
@[reassoc] theorem representedCMNormalGraph_refinement (g : SmallCMResidualGroup D U W) :
    graph R U W (hWV.trans hVU) g ≫ kernelRefinement R U V hVU W hWV =
      (refinement R U V W hVU hWV).hom ≫ graph R U V hVU (quotientMap g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, representedCMNormalKernelPairRefinement_fst,
      representedCMNormalGraph_fst_assoc, representedCMNormalGraph_fst]
    exact (Category.comp_id _).symm
  · simp only [Category.assoc, representedCMNormalKernelPairRefinement_snd,
      representedCMNormalGraph_snd_assoc, representedCMNormalGraph_snd]
    have hc := (refinement R U V W hVU hWV).comm g
    dsimp only [Action.res, MonoidHom.comp] at hc
    exact hc

/-- The actual coproduct-to-kernel-pair comparison commutes with normal refinement. -/
@[reassoc] theorem representedCMNormalKernelComparison_refinement :
    copiesRefinement R U V hVU W hWV ≫ kernelComparison R U V hVU =
      kernelComparison R U W (hWV.trans hVU) ≫ kernelRefinement R U V hVU W hWV := by
  apply Sigma.hom_ext
  intro g
  simp only [representedCMNormalCopiesRefinement_ι_assoc,
    representedCMNormalKernelComparison_ι, representedCMNormalKernelComparison_ι_assoc]
  exact (representedCMNormalGraph_refinement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R U V hVU W hWV g).symm

/-- Identity refinement is the identity on the actual disjoint union. -/
@[simp] theorem representedCMNormalCopiesRefinement_refl :
    copiesRefinement R U V hVU V (le_refl _) = 𝟙 (copies R U V) := by
  apply Sigma.hom_ext
  intro g
  rw [representedCMNormalCopiesRefinement_ι, representedCMNormalRefinement_refl,
    smallCMResidualQuotientMap_refl]
  exact (Category.id_comp
    (Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) g)).trans
      (Category.comp_id _).symm

/-- Identity refinement is the identity on the actual kernel pair. -/
@[simp] theorem representedCMNormalKernelPairRefinement_refl :
    kernelRefinement R U V hVU V (le_refl _) = 𝟙 (kernelPair R U V hVU) := by
  apply pullback.hom_ext
  · rw [representedCMNormalKernelPairRefinement_fst, Category.id_comp,
      representedCMNormalRefinement_refl]
    exact Category.comp_id _
  · rw [representedCMNormalKernelPairRefinement_snd, Category.id_comp,
      representedCMNormalRefinement_refl]
    exact Category.comp_id _

variable (Z : SmallCMLevel D) (hZW : Z.obj.subgroup ≤ W.obj.subgroup)
  [(Z.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Successive copy refinements equal the direct actual refinement. -/
@[reassoc] theorem representedCMNormalCopiesRefinement_comp :
    copiesRefinement R U W (hWV.trans hVU) Z hZW ≫
        copiesRefinement R U V hVU W hWV =
      copiesRefinement R U V hVU Z (hZW.trans hWV) := by
  apply Sigma.hom_ext
  intro g
  simp only [representedCMNormalCopiesRefinement_ι_assoc,
    representedCMNormalCopiesRefinement_ι]
  rw [← Category.assoc, representedCMNormalRefinement_comp]
  congr 2
  exact congrArg (fun f : SmallCMResidualGroup D U Z →* SmallCMResidualGroup D U V => f g)
    (smallCMResidualQuotientMap_comp D U V W Z hWV hZW)

/-- Successive kernel-pair refinements equal the direct actual refinement. -/
@[reassoc] theorem representedCMNormalKernelPairRefinement_comp :
    kernelRefinement R U W (hWV.trans hVU) Z hZW ≫
        kernelRefinement R U V hVU W hWV =
      kernelRefinement R U V hVU Z (hZW.trans hWV) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, representedCMNormalKernelPairRefinement_fst,
      representedCMNormalKernelPairRefinement_snd,
      representedCMNormalKernelPairRefinement_fst_assoc,
      representedCMNormalKernelPairRefinement_snd_assoc,
      representedCMNormalRefinement_comp]

end Refinement

section RepresentationComparison

variable (R' : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "compareReps" => representedCMSchemeTowerComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor R R'

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
/-- The canonical representation comparison acts on each actual residual-indexed summand. -/
def representedCMNormalCopiesComparison : copies R U V ≅ copies R' U V :=
  Sigma.mapIso (fun _ : SmallCMResidualGroup D U V => (compareReps).app V)

local notation "copiesComparison" => representedCMNormalCopiesComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
@[reassoc (attr := simp)] theorem representedCMNormalCopiesComparison_ι_hom
    (g : SmallCMResidualGroup D U V) :
    Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) g ≫
        (copiesComparison R U V R').hom =
      (compareReps).hom.app V ≫
        Sigma.ι (fun _ : SmallCMResidualGroup D U V => (schemes R').obj V) g :=
  Sigma.ι_mapIso_hom _ _

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
/-- Canonical changes of the exact representing schemes identify their actual kernel pairs. -/
def representedCMNormalKernelPairComparison :
    kernelPair R U V hVU ≅ kernelPair R' U V hVU where
  hom := pullback.lift
    (pullback.fst _ _ ≫ (compareReps).hom.app V)
    (pullback.snd _ _ ≫ (compareReps).hom.app V) (by
      have hc : (compareReps).hom.app V ≫ projection R' U V hVU =
          projection R U V hVU ≫ (compareReps).hom.app U :=
        ((compareReps).hom.naturality (smallCMInclusion D hVU)).symm
      simp only [Category.assoc, hc, pullback.condition_assoc])
  inv := pullback.lift
    (pullback.fst _ _ ≫ (compareReps).inv.app V)
    (pullback.snd _ _ ≫ (compareReps).inv.app V) (by
      have hc : (compareReps).inv.app V ≫ projection R U V hVU =
          projection R' U V hVU ≫ (compareReps).inv.app U :=
        ((compareReps).inv.naturality (smallCMInclusion D hVU)).symm
      simp only [Category.assoc, hc, pullback.condition_assoc])
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [Category.assoc]

local notation "kernelPairComparison" => representedCMNormalKernelPairComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
@[reassoc (attr := simp)] theorem representedCMNormalKernelPairComparison_hom_fst :
    (kernelPairComparison R U V hVU R').hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (compareReps).hom.app V :=
  pullback.lift_fst _ _ _

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
@[reassoc (attr := simp)] theorem representedCMNormalKernelPairComparison_hom_snd :
    (kernelPairComparison R U V hVU R').hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (compareReps).hom.app V :=
  pullback.lift_snd _ _ _

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
@[reassoc (attr := simp)] theorem representedCMNormalKernelPairComparison_inv_fst :
    (kernelPairComparison R U V hVU R').inv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (compareReps).inv.app V :=
  pullback.lift_fst _ _ _

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
@[reassoc (attr := simp)] theorem representedCMNormalKernelPairComparison_inv_snd :
    (kernelPairComparison R U V hVU R').inv ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (compareReps).inv.app V :=
  pullback.lift_snd _ _ _

/-- The canonical comparison of quotient actions identifies each residual graph. -/
@[reassoc] theorem representedCMNormalGraph_comparison (g : SmallCMResidualGroup D U V) :
    graph R U V hVU g ≫ (kernelPairComparison R U V hVU R').hom =
      (compareReps).hom.app V ≫ graph R' U V hVU g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, representedCMNormalKernelPairComparison_hom_fst,
      representedCMNormalGraph_fst_assoc, representedCMNormalGraph_fst]
    exact (Category.comp_id _).symm
  · simp only [Category.assoc, representedCMNormalKernelPairComparison_hom_snd,
      representedCMNormalGraph_snd_assoc, representedCMNormalGraph_snd]
    exact (representedCMNormalQuotientActionComparison D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU R').hom.comm g

/-- Canonical changes of the exact representations preserve the constructed comparison. -/
@[reassoc] theorem representedCMNormalKernelComparison_comparison :
    (copiesComparison R U V R').hom ≫ kernelComparison R' U V hVU =
      kernelComparison R U V hVU ≫ (kernelPairComparison R U V hVU R').hom := by
  apply Sigma.hom_ext
  intro g
  simp only [representedCMNormalCopiesComparison_ι_hom_assoc,
    representedCMNormalKernelComparison_ι, representedCMNormalKernelComparison_ι_assoc]
  exact (representedCMNormalGraph_comparison D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R U V hVU R' g).symm

end RepresentationComparison

/-- The actual normal-cover comparison from precisely the existing representability target. -/
def cmNormalKernelComparison
    (q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) :=
  kernelComparison (chosenCMLevelRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q) U V hVU

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
