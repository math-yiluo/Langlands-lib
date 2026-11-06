import Langlands.Shimura.CompactOpenNormalRefinement
import Langlands.Shimura.PEL.HarrisTaylorCMNormalSmoothEtale
import Langlands.Shimura.PEL.HarrisTaylorCMConjugationSchemes
import Langlands.AlgebraicGeometry.FiniteEtaleSourceUnramified

/-! # Finite-etale geometry of every actual CM transporter -/

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

/-- A compact open normal refinement remains sufficiently small by containment. -/
def smallCMNormalRefinement (U V : SmallCMLevel D) : SmallCMLevel D := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  let W := CompactOpenLevel.normalRefinement U.obj V.obj
  exact ⟨W.level, V.property.mono W.le_fine⟩

omit [IsCMField F] [IsScalarTower E F A] in
theorem smallCMNormalRefinement_le_coarse (U V : SmallCMLevel D) :
    (smallCMNormalRefinement D U V).obj.subgroup ≤ U.obj.subgroup := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  exact (CompactOpenLevel.normalRefinement U.obj V.obj).le_coarse

omit [IsCMField F] [IsScalarTower E F A] in
theorem smallCMNormalRefinement_le_fine (U V : SmallCMLevel D) :
    (smallCMNormalRefinement D U V).obj.subgroup ≤ V.obj.subgroup := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  exact (CompactOpenLevel.normalRefinement U.obj V.obj).le_fine

omit [IsCMField F] [IsScalarTower E F A] in
instance smallCMNormalRefinement_normal_coarse (U V : SmallCMLevel D) :
    ((smallCMNormalRefinement D U V).obj.subgroup.subgroupOf U.obj.subgroup).Normal := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  exact (CompactOpenLevel.normalRefinement U.obj V.obj).normal_coarse

omit [IsCMField F] [IsScalarTower E F A] in
theorem smallCMNormalRefinement_normal_fine (U V : SmallCMLevel D)
    (hVU : V.obj.subgroup ≤ U.obj.subgroup) :
    ((smallCMNormalRefinement D U V).obj.subgroup.subgroupOf V.obj.subgroup).Normal := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  exact (CompactOpenLevel.normalRefinement U.obj V.obj).normal_fine hVU

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "normalEtale" => representedCMNormalProjection_etale_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry
  stability square universality dualityNaturality polarizationStability compatibility h htor
local notation "normalOpen" => representedCMNormalProjection_isOpenMap
  D C preservation composition unitCoherence associativity comparison symmetry
  stability square universality dualityNaturality polarizationStability compatibility h htor
local notation "Rigid" => CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "surjectiveMap" => representedCMSchemeTower_map_surjective D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor

/-- Forgetting along any small-level inclusion is etale: detect unramifiedness
and openness after an actual common normal refinement. -/
theorem representedCMInclusion_etale_of_dominantCriterion
    (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigidU : Rigid U.obj) (hRigidV : Rigid V.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    Etale ((schemes R).map (smallCMInclusion D hVU)) := by
  let W := smallCMNormalRefinement D U V
  have hWU : W.obj.subgroup ≤ U.obj.subgroup :=
    smallCMNormalRefinement_le_coarse D U V
  have hWV : W.obj.subgroup ≤ V.obj.subgroup :=
    smallCMNormalRefinement_le_fine D U V
  let : (W.obj.subgroup.subgroupOf U.obj.subgroup).Normal :=
    smallCMNormalRefinement_normal_coarse D U V
  let : (W.obj.subgroup.subgroupOf V.obj.subgroup).Normal :=
    smallCMNormalRefinement_normal_fine D U V hVU
  let p := (schemes R).map (smallCMInclusion D hWV)
  let f := (schemes R).map (smallCMInclusion D hVU)
  have hcomp : p ≫ f = (schemes R).map (smallCMInclusion D hWU) := by
    dsimp [p, f]
    rw [← (schemes R).map_comp, smallCMInclusion_trans]
  have : Etale p := normalEtale R V W hWV existence geometry hRigidV criterion
  have : IsFinite p :=
    representedCMSchemeTower_map_isFinite D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R (smallCMInclusion D hWV)
  have hp : Function.Surjective p :=
    surjectiveMap R existence geometry (smallCMInclusion D hWV)
  have : Surjective p := ⟨hp⟩
  have : Etale (p ≫ f) := by
    rw [hcomp]
    exact normalEtale R U W hWU existence geometry hRigidU criterion
  have : FormallyUnramified f := formallyUnramified_of_finiteEtale_comp p f
  have hopen : IsOpenMap f := by
    apply IsOpenMap.of_comp p.continuous hp
    change IsOpenMap (p ≫ f)
    rw [hcomp]
    exact normalOpen R U W hWU existence geometry
  have : Smooth (R V).base.obj.hom := (R V).smooth
  have : Smooth (R U).base.obj.hom := (R U).smooth
  exact openUnramifiedSmooth_etale_of_dominantCriterion criterion
    ((schemes R).obj V) ((schemes R).obj U)
    (R V).base.obj.hom (R U).base.obj.hom f hopen

omit [IsCMField F] [IsScalarTower E F A] in
/-- The actual conjugated source of a transporter is contained in its target. -/
theorem smallCMTransporter_conjugate_le {U V : SmallCMLevel D} (k : V ⟶ U) :
    (smallCMConjugateLevel D V k.hom.element).obj.subgroup ≤ U.obj.subgroup := by
  intro x hx
  have hx' : k.hom.element * x * k.hom.element⁻¹ ∈ V.obj.subgroup := hx
  have := k.hom.respects _ hx'
  simpa [mul_assoc] using this

omit [IsCMField F] [IsScalarTower E F A] in
/-- A transporter factors through the genuine conjugation isomorphism and
the identity-element inclusion of its conjugated source. -/
theorem smallCMTransporter_factorization {U V : SmallCMLevel D} (k : V ⟶ U) :
    (smallCMConjugationIso D V k.hom.element).hom ≫
        smallCMInclusion D (smallCMTransporter_conjugate_le D k) = k := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  exact mul_one _

/-- Every original represented transporter is etale under the same named
geometric prerequisites, with rigidity retained at all small levels. -/
theorem representedCMSchemeTower_map_etale_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : ∀ U : SmallCMLevel D, Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0})
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    Etale ((schemes R).map k) := by
  let i := smallCMInclusion D (smallCMTransporter_conjugate_le D k)
  have : Etale ((schemes R).map i) :=
    representedCMInclusion_etale_of_dominantCriterion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R
      U (smallCMConjugateLevel D V k.hom.element)
      (smallCMTransporter_conjugate_le D k)
      existence geometry (hRigid U) (hRigid _) criterion
  rw [← smallCMTransporter_factorization D k, (schemes R).map_comp]
  infer_instance

/-- The identical original transporter as an actual finite-etale cover. -/
def representedCMFiniteEtaleTransition_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : ∀ U : SmallCMLevel D, Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0})
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    Cover ((schemes R).obj U) := by
  have : Etale ((schemes R).map k) :=
    representedCMSchemeTower_map_etale_of_dominantCriterion D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor R
      existence geometry hRigid criterion k
  exact representedCMFiniteEtaleTransition D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R k

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : DominantUnramifiedEtaleStatement.{0})

include existence geometry hRigid criterion

local notation "representedCover" =>
  representedCMFiniteEtaleTransition_of_dominantCriterion D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R existence geometry hRigid criterion

/-- Finiteness holds for every original represented transporter under these inputs. -/
theorem representedCMSchemeTower_map_isFinite_of_dominantCriterion
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    IsFinite ((schemes R).map k) :=
  (representedCover k).property.1

@[simp] theorem representedCMFiniteEtaleTransition_of_dominantCriterion_left
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (representedCover k).obj.left = (schemes R).obj V := rfl

@[simp] theorem representedCMFiniteEtaleTransition_of_dominantCriterion_hom
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (representedCover k).obj.hom = (schemes R).map k := rfl

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- Every transporter of the exact chosen tower is etale under the named inputs. -/
theorem cmSchemeTower_map_etale_of_dominantCriterion
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    Etale ((chosenSchemes).map k) :=
  representedCMSchemeTower_map_etale_of_dominantCriterion D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    chosenReps existence geometry hRigid criterion k

/-- Every transporter of the exact chosen tower is finite under the named inputs. -/
theorem cmSchemeTower_map_isFinite_of_dominantCriterion
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    IsFinite ((chosenSchemes).map k) :=
  representedCMSchemeTower_map_isFinite_of_dominantCriterion D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    chosenReps existence geometry hRigid criterion k

/-- The identical chosen tower transition as a finite-etale cover. -/
def cmFiniteEtaleTransition_of_dominantCriterion
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    Cover ((chosenSchemes).obj U) :=
  representedCMFiniteEtaleTransition_of_dominantCriterion D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    chosenReps existence geometry hRigid criterion k

local notation "chosenCover" => cmFiniteEtaleTransition_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  existence geometry hRigid criterion q

@[simp] theorem cmFiniteEtaleTransition_of_dominantCriterion_left
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (chosenCover k).obj.left = (chosenSchemes).obj V := rfl

@[simp] theorem cmFiniteEtaleTransition_of_dominantCriterion_hom
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (chosenCover k).obj.hom = (chosenSchemes).map k := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
