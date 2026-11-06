import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientCoarseRestriction
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficientDiagram

/-! # Actual geometric CM intersection covers over a smaller coarse level -/

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

local notation "fieldProjection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

local notation "levels" => cmHarrisCoarseCoefficientLevels D ρ p U V hVU m hm
local notation "groups" => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm
local notation "T" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U V hVU m hm k
local notation "hT" k:arg => cmHarrisCoarseCoefficientLevel_le_coarse D ρ p U V hVU m hm k
local notation "originalT" k:arg => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "originalhT" k:arg => cmHarrisCoefficientLevel_le D ρ p U m hm k
local notation "hOriginal" k:arg =>
  cmHarrisCoarseCoefficientLevel_le_original D ρ p U V hVU m hm k
local notation "hincl" f:arg =>
  cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom (f).unop)
local notation "originalGroups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "groupInclusion" k:arg =>
  cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm k
local notation "XV" => (geometricSchemes).obj V
local notation "XU" => (geometricSchemes).obj U
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hVU)
local notation "geometricAction" k:arg => cmGeometricNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q V (T k) (hT k)

/-- The actual intersection schemes carry the original inverse-right residual actions. -/
def cmHarrisGeometricCoarseSchemeDiagram : EquivariantDiagram groups Scheme where
  obj := levels ⋙ geometricSchemes
  ρ k := (geometricAction k.unop).ρ
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D V (T i.unop) (hT i.unop) g) ≫
          (geometricSchemes).map (smallCMInclusion D (hincl f)) =
        (geometricSchemes).map (smallCMInclusion D (hincl f)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D V (T j.unop) (hT j.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "schemeDiagram" => cmHarrisGeometricCoarseSchemeDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU ρ p m hm

/-- Projection from the actual intersection schemes to the exact geometric level V. -/
def cmHarrisGeometricCoarseSchemeProjection :
    (schemeDiagram).obj ⟶ (Functor.const ℕᵒᵖ).obj XV where
  app k := (geometricSchemes).map (smallCMInclusion D (hT k.unop))
  naturality i j f := by
    dsimp [cmHarrisGeometricCoarseSchemeDiagram, cmHarrisCoarseCoefficientLevels]
    rw [Category.comp_id, ← (geometricSchemes).map_comp, smallCMInclusion_trans]

local notation "projection" => cmHarrisGeometricCoarseSchemeProjection D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU ρ p m hm

/-- The deck action fixes the original projection to V. -/
@[reassoc] theorem cmHarrisGeometricCoarseSchemeProjection_invariant
    (k : ℕᵒᵖ) (g : (groups).obj k) :
    (schemeDiagram).ρ k g ≫ (projection).app k = (projection).app k :=
  cmGeometricNormalProjection_invariant D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q V (T k.unop) (hT k.unop) g

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigidV : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor V.obj)

/-- Finite geometric torsors on the named intersections, with no new lattice. -/
def cmHarrisGeometricCoarseTorsor (k : ℕ) :
    {Y : Action (XV).Etale (SmallCMResidualGroup D V (T k)) //
      IsFiniteGeometricTorsor XV Y} :=
  cmGeometricNormalGeometricTorsor_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q V (T k) (hT k)
    existence geometry hRigidV DominantUnramifiedEtaleProof.dominantUnramifiedEtale

local notation "torsor" k:arg => cmHarrisGeometricCoarseTorsor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV k

/-- Every actual intersection-level forgetting map is a morphism over V. -/
def cmHarrisGeometricCoarseEtaleTower : ℕᵒᵖ ⥤ (XV).Etale where
  obj k := (torsor k.unop).val.V
  map {i j} f := MorphismProperty.Over.homMk ((schemeDiagram).obj.map f) (by
    change (schemeDiagram).obj.map f ≫ (projection).app j = (projection).app i
    exact ((projection).naturality f).trans (Category.comp_id _))
  map_id k := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).obj.map_id k
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).obj.map_comp f g

local notation "etaleTower" => cmHarrisGeometricCoarseEtaleTower D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV

/-- The original intersection covers form a genuine varying-group cover diagram. -/
def cmHarrisGeometricCoarseEtaleDiagram : EquivariantDiagram groups (XV).Etale where
  obj := etaleTower
  ρ k := (torsor k.unop).val.ρ
  comm f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).comm f g

local notation "etaleDiagram" => cmHarrisGeometricCoarseEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV

@[simp] theorem cmHarrisGeometricCoarseEtaleDiagram_left (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).left = (geometricSchemes).obj (T k.unop) := rfl

@[simp] theorem cmHarrisGeometricCoarseEtaleDiagram_hom (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).hom = (projection).app k := rfl

@[simp] theorem cmHarrisGeometricCoarseEtaleDiagram_map_left
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((etaleDiagram).obj.map f).left =
      (geometricSchemes).map (smallCMInclusion D (hincl f)) := rfl

@[simp] theorem cmHarrisGeometricCoarseEtaleDiagram_action_mk_left
    (k : ℕᵒᵖ) (g : V.obj.subgroup) :
    ((etaleDiagram).ρ k (QuotientGroup.mk g)).left =
      (geometricSchemes).map
        (smallCMNormalInverseArrow D V (T k.unop) (hT k.unop) g) := rfl

/-- The finite geometric torsor condition is derived for every named component. -/
theorem cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor (k : ℕᵒᵖ) :
    IsFiniteGeometricTorsor XV ((etaleDiagram).action k) := (torsor k.unop).property

variable (hRigidU : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "originalDiagram" => cmHarrisGeometricCoefficientEtaleDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigidU
local notation "pulledDiagram" =>
  (etaleTorsorDiagramPullback coarseMap originalGroups).obj originalDiagram

/-- The exact original intersection map gives the first coordinate of the comparison. -/
def cmHarrisGeometricCoarseFineMap (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).left ⟶ ((originalDiagram).obj.obj k).left :=
  (geometricSchemes).map (smallCMInclusion D (hOriginal k.unop))

local notation "fineMap" k:arg => cmHarrisGeometricCoarseFineMap D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU k

/-- Both routes from the intersection scheme to the original coarse U agree. -/
@[reassoc] theorem cmHarrisGeometricCoarseFineMap_projection (k : ℕᵒᵖ) :
    fineMap k ≫ ((originalDiagram).obj.obj k).hom =
      ((etaleDiagram).obj.obj k).hom ≫ coarseMap := by
  change (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _) =
    (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _)
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- Actual map to the fiber-product cover, induced by the original two projections. -/
def cmHarrisGeometricCoarsePullbackCoverMap (k : ℕᵒᵖ) :
    (etaleDiagram).obj.obj k ⟶ (pulledDiagram).obj.obj k :=
  MorphismProperty.Over.homMk
    (pullback.lift (fineMap k) (((etaleDiagram).obj.obj k).hom)
      (cmHarrisGeometricCoarseFineMap_projection D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
        existence geometry hRigidV hRigidU k))
    (pullback.lift_snd _ _ _)

local notation "coverMap" k:arg => cmHarrisGeometricCoarsePullbackCoverMap D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU k

@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarsePullbackCoverMap_fst (k : ℕᵒᵖ) :
    (coverMap k).left ≫ pullback.fst ((originalDiagram).obj.obj k).hom coarseMap =
      fineMap k := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarsePullbackCoverMap_snd (k : ℕᵒᵖ) :
    (coverMap k).left ≫ pullback.snd ((originalDiagram).obj.obj k).hom coarseMap =
      ((etaleDiagram).obj.obj k).hom := pullback.lift_snd _ _ _

/-- The fine-level comparison respects the constructed residual-group embedding. -/
@[reassoc] theorem cmHarrisGeometricCoarseFineMap_equivariant
    (k : ℕᵒᵖ) (g : (groups).obj k) :
    ((etaleDiagram).ρ k g).left ≫ fineMap k =
      fineMap k ≫ ((originalDiagram).ρ k ((groupInclusion k) g)).left := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    change (geometricSchemes).map
        (smallCMNormalInverseArrow D V (T k.unop) (hT k.unop) g) ≫
        (geometricSchemes).map (smallCMInclusion D (hOriginal k.unop)) =
      (geometricSchemes).map (smallCMInclusion D (hOriginal k.unop)) ≫
        (geometricSchemes).map (smallCMNormalInverseArrow D U (originalT k.unop)
          (originalhT k.unop) (Subgroup.inclusion hVU g))
    rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp]
    apply congrArg (geometricSchemes).map
    apply ObjectProperty.hom_ext
    apply CompactOpenLevel.Arrow.ext
    exact (mul_one _).trans (one_mul _).symm

/-- The actual fiber-product comparison is equivariant under the residual embedding. -/
def cmHarrisGeometricCoarsePullbackActionMap (k : ℕᵒᵖ) :
    (etaleDiagram).action k ⟶
      (Action.res (XV).Etale (groupInclusion k)).obj ((pulledDiagram).action k) where
  hom := coverMap k
  comm g := by
    apply MorphismProperty.Over.Hom.ext
    change ((etaleDiagram).ρ k g).left ≫ (coverMap k).left =
      (coverMap k).left ≫ ((pulledDiagram).ρ k ((groupInclusion k) g)).left
    have hfst : ((pulledDiagram).ρ k ((groupInclusion k) g)).left ≫
        pullback.fst ((originalDiagram).obj.obj k).hom coarseMap =
      pullback.fst ((originalDiagram).obj.obj k).hom coarseMap ≫
        ((originalDiagram).ρ k ((groupInclusion k) g)).left :=
      etaleTorsorPullbackFunctor_ρ_fst coarseMap
        ((originalDiagram).action k) ((groupInclusion k) g)
    have hsnd : ((pulledDiagram).ρ k ((groupInclusion k) g)).left ≫
        pullback.snd ((originalDiagram).obj.obj k).hom coarseMap =
      pullback.snd ((originalDiagram).obj.obj k).hom coarseMap :=
      etaleTorsorPullbackFunctor_ρ_snd coarseMap
        ((originalDiagram).action k) ((groupInclusion k) g)
    apply pullback.hom_ext
    · rw [Category.assoc, cmHarrisGeometricCoarsePullbackCoverMap_fst,
        Category.assoc, hfst,
        ← Category.assoc, cmHarrisGeometricCoarsePullbackCoverMap_fst]
      exact cmHarrisGeometricCoarseFineMap_equivariant D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
        existence geometry hRigidV hRigidU k g
    · rw [Category.assoc, cmHarrisGeometricCoarsePullbackCoverMap_snd,
        Category.assoc, hsnd,
        cmHarrisGeometricCoarsePullbackCoverMap_snd]
      exact MorphismProperty.Over.w ((etaleDiagram).ρ k g)


/-- Original forgetting maps commute with both intersection-level projections. -/
@[reassoc] theorem cmHarrisGeometricCoarseFineMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((etaleDiagram).obj.map f).left ≫ fineMap j =
      fineMap i ≫ ((originalDiagram).obj.map f).left := by
  change (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _) =
    (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _)
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- The literal pullback transition retains the original first coordinate. -/
@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarsePulledMap_fst
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((pulledDiagram).obj.map f).left ≫
        pullback.fst ((originalDiagram).obj.obj j).hom coarseMap =
      pullback.fst ((originalDiagram).obj.obj i).hom coarseMap ≫
        ((originalDiagram).obj.map f).left := by
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_fst _ _ _

/-- The literal pullback transition fixes the smaller coarse coordinate. -/
@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarsePulledMap_snd
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((pulledDiagram).obj.map f).left ≫
        pullback.snd ((originalDiagram).obj.obj j).hom coarseMap =
      pullback.snd ((originalDiagram).obj.obj i).hom coarseMap := by
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_snd _ _ _

/-- All comparison components commute with the original exponent maps. -/
@[reassoc] theorem cmHarrisGeometricCoarsePullbackCoverMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (etaleDiagram).obj.map f ≫ coverMap j =
      coverMap i ≫ (pulledDiagram).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change ((etaleDiagram).obj.map f).left ≫ (coverMap j).left =
    (coverMap i).left ≫ ((pulledDiagram).obj.map f).left
  apply pullback.hom_ext
  · rw [Category.assoc, cmHarrisGeometricCoarsePullbackCoverMap_fst,
      Category.assoc, cmHarrisGeometricCoarsePulledMap_fst,
      ← Category.assoc, cmHarrisGeometricCoarsePullbackCoverMap_fst]
    exact cmHarrisGeometricCoarseFineMap_naturality D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
      existence geometry hRigidV hRigidU f
  · rw [Category.assoc, cmHarrisGeometricCoarsePullbackCoverMap_snd,
      Category.assoc, cmHarrisGeometricCoarsePulledMap_snd,
      cmHarrisGeometricCoarsePullbackCoverMap_snd]
    exact MorphismProperty.Over.w ((etaleDiagram).obj.map f)

/-- A constructed comparison of the whole actual cover towers over V. -/
def cmHarrisGeometricCoarsePullbackTowerMap :
    (etaleDiagram).obj ⟶ (pulledDiagram).obj where
  app k := coverMap k
  naturality _i _j f := cmHarrisGeometricCoarsePullbackCoverMap_naturality D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    q U V hVU ρ p m hm existence geometry hRigidV hRigidU f

/-- Every pulled original G-torsor is a finite geometric torsor over V. -/
theorem cmHarrisGeometricCoarsePulledDiagram_isFiniteGeometricTorsor (k : ℕᵒᵖ) :
    IsFiniteGeometricTorsor XV ((pulledDiagram).action k) :=
  etaleTorsorDiagramPullback_isFiniteGeometricTorsor coarseMap originalGroups
    originalDiagram (cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor
      D C preservation composition unitCoherence associativity comparison symmetry
      stability square universality dualityNaturality polarizationStability compatibility
      h htor q U ρ p m hm existence geometry hRigidU) k

/-- The named intersection covers cover the final object of the small-etale site of V. -/
theorem cmHarrisGeometricCoarseEtaleDiagram_coversTop (k : ℕᵒᵖ) :
    (Scheme.smallEtaleTopology XV).CoversTop
      (fun _ : Unit => (etaleDiagram).obj.obj k) :=
  etale_coversTop_of_surjective (torsor k.unop).val.V (torsor k.unop).property.2.2.1

/-- The pulled original covers also cover the final object of that same site. -/
theorem cmHarrisGeometricCoarsePulledDiagram_coversTop (k : ℕᵒᵖ) :
    (Scheme.smallEtaleTopology XV).CoversTop
      (fun _ : Unit => (pulledDiagram).obj.obj k) :=
  etale_coversTop_of_surjective ((pulledDiagram).obj.obj k)
    (cmHarrisGeometricCoarsePulledDiagram_isFiniteGeometricTorsor D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor q U V
      hVU ρ p m hm existence geometry hRigidU k).2.2.1

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
