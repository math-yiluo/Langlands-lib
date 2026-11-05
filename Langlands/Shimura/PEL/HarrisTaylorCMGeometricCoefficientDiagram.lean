import Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalTorsor
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSchemes

/-! # Full coefficient-cover diagrams on the exact geometric CM levels -/

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

variable (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

local notation "levels" => cmHarrisCoefficientLevels D ρ p U m hm
local notation "groups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "Vcoeff" k => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "hcoeff" k => cmHarrisCoefficientLevel_le D ρ p U m hm k
local notation "hincl" f => cmHarrisCoefficientLevel_antitone D ρ p U m hm (leOfHom (f).unop)
local notation "X" => (schemes).obj U
local notation "Xbar" => (geometricSchemes).obj U
local notation "geometricAction" k => cmGeometricNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U (Vcoeff k) (hcoeff k)

/-- The actual geometric scheme tower at the original full coefficient kernel levels,
with the original inverse-right residual actions. -/
def cmHarrisGeometricCoefficientSchemeDiagram : EquivariantDiagram groups Scheme where
  obj := levels ⋙ geometricSchemes
  ρ k := (geometricAction k.unop).ρ
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D U (Vcoeff i.unop) (hcoeff i.unop) g) ≫
          (geometricSchemes).map (smallCMInclusion D (hincl f)) =
        (geometricSchemes).map (smallCMInclusion D (hincl f)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D U (Vcoeff j.unop) (hcoeff j.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "schemeDiagram" => cmHarrisGeometricCoefficientSchemeDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm

/-- No new levels or transition maps are selected by the geometric diagram. -/
@[simp] theorem cmHarrisGeometricCoefficientSchemeDiagram_obj :
    (schemeDiagram).obj = levels ⋙ geometricSchemes := rfl

@[simp] theorem cmHarrisGeometricCoefficientSchemeDiagram_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (schemeDiagram).obj.map f =
      (geometricSchemes).map (smallCMInclusion D (hincl f)) := rfl

/-- All coefficient covers project to the same existing geometric coarse level. -/
def cmHarrisGeometricCoefficientSchemeProjection :
    (schemeDiagram).obj ⟶ (Functor.const ℕᵒᵖ).obj Xbar where
  app k := (geometricSchemes).map (smallCMInclusion D (hcoeff k.unop))
  naturality i j f := by
    dsimp [cmHarrisGeometricCoefficientSchemeDiagram, cmHarrisCoefficientLevels]
    rw [Category.comp_id, ← (geometricSchemes).map_comp, smallCMInclusion_trans]

local notation "projection" => cmHarrisGeometricCoefficientSchemeProjection D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm

/-- Every residual action fixes the exact geometric coarse projection. -/
@[reassoc] theorem cmHarrisGeometricCoefficientSchemeProjection_invariant
    (k : ℕᵒᵖ) (g : (groups).obj k) :
    (schemeDiagram).ρ k g ≫ (projection).app k = (projection).app k :=
  cmGeometricNormalProjection_invariant D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U (Vcoeff k.unop) (hcoeff k.unop) g

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

/-- The exact geometric finite torsor at the full original Harris coefficient kernel.
The published dominant-unramified criterion discharges that generic premise. -/
def cmHarrisGeometricCoefficientTorsor (k : ℕ) :
    {Y : Action (Xbar).Etale (SmallCMResidualGroup D U (Vcoeff k)) //
      IsFiniteGeometricTorsor Xbar Y} :=
  cmGeometricNormalGeometricTorsor_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U (Vcoeff k)
    (hcoeff k) existence geometry hRigid
    DominantUnramifiedEtaleProof.dominantUnramifiedEtale

local notation "torsor" k => cmHarrisGeometricCoefficientTorsor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k

/-- The exact geometric coefficient covers and original forgetting maps in the
small-etale category of the same geometric coarse level. -/
def cmHarrisGeometricCoefficientEtaleTower : ℕᵒᵖ ⥤ (Xbar).Etale where
  obj k := (torsor k.unop).val.V
  map {i j} f := MorphismProperty.Over.homMk ((schemeDiagram).obj.map f) (by
    change (schemeDiagram).obj.map f ≫ (projection).app j = (projection).app i
    have e := (projection).naturality f
    change (schemeDiagram).obj.map f ≫ (projection).app j =
      (projection).app i ≫ 𝟙 Xbar at e
    exact e.trans (Category.comp_id _))
  map_id k := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).obj.map_id k
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).obj.map_comp f g

local notation "etaleTower" => cmHarrisGeometricCoefficientEtaleTower D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The exact geometric coefficient torsors form a varying-group equivariant diagram. -/
def cmHarrisGeometricCoefficientEtaleDiagram : EquivariantDiagram groups (Xbar).Etale where
  obj := etaleTower
  ρ k := (torsor k.unop).val.ρ
  comm f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).comm f g

local notation "etaleDiagram" => cmHarrisGeometricCoefficientEtaleDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

@[simp] theorem cmHarrisGeometricCoefficientEtaleDiagram_action (k : ℕᵒᵖ) :
    (etaleDiagram).action k = (torsor k.unop).val := rfl

@[simp] theorem cmHarrisGeometricCoefficientEtaleDiagram_obj_left (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).left = (geometricSchemes).obj (Vcoeff k.unop) := rfl

@[simp] theorem cmHarrisGeometricCoefficientEtaleDiagram_obj_hom (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).hom = (projection).app k := rfl

@[simp] theorem cmHarrisGeometricCoefficientEtaleDiagram_map_left
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((etaleDiagram).obj.map f).left =
      (geometricSchemes).map (smallCMInclusion D (hincl f)) := rfl

/-- Each deck transformation is the existing inverse-right geometric tower map. -/
@[simp] theorem cmHarrisGeometricCoefficientEtaleDiagram_action_mk_left
    (k : ℕᵒᵖ) (g : U.obj.subgroup) :
    ((etaleDiagram).ρ k (QuotientGroup.mk g)).left =
      (geometricSchemes).map
        (smallCMNormalInverseArrow D U (Vcoeff k.unop) (hcoeff k.unop) g) := rfl

/-- The finite geometric torsor condition is proved for every exact component. -/
theorem cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor (k : ℕᵒᵖ) :
    IsFiniteGeometricTorsor Xbar ((etaleDiagram).action k) :=
  (torsor k.unop).property

/-- Each exact geometric coefficient cover covers the final object of its small-etale site. -/
theorem cmHarrisGeometricCoefficientEtaleDiagram_coversTop (k : ℕᵒᵖ) :
    (Scheme.smallEtaleTopology Xbar).CoversTop
      (fun _ : Unit => (etaleDiagram).obj.obj k) :=
  etale_coversTop_of_surjective (torsor k.unop).val.V (torsor k.unop).property.2.2.1

local notation "originalDiagram" => cmHarrisCoefficientEtaleDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "π" => (fieldProjection).app U
local notation "pulledDiagram" =>
  (etaleTorsorDiagramPullback π groups).obj originalDiagram
local notation "normalSquare" k => cmGeometricSchemeTower_map_isPullback D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q (smallCMInclusion D (hcoeff (k).unop))

/-- The canonical equivariant cartesian comparison at each original coefficient level. -/
def cmHarrisGeometricCoefficientEtaleActionPullbackIso (k : ℕᵒᵖ) :
    (etaleDiagram).action k ≅ (pulledDiagram).action k :=
  cmGeometricNormalEtaleActionPullbackIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U (Vcoeff k.unop) (hcoeff k.unop)
    existence geometry hRigid DominantUnramifiedEtaleProof.dominantUnramifiedEtale

local notation "componentIso" k => cmHarrisGeometricCoefficientEtaleActionPullbackIso
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid k

/-- The canonical component comparisons commute with all original coefficient
forgetting maps, as maps of actual small-etale objects. -/
def cmHarrisGeometricCoefficientEtaleTowerPullbackIso :
    (etaleDiagram).obj ≅ (pulledDiagram).obj :=
  NatIso.ofComponents
    (fun k => (Action.forget (Xbar).Etale ((groups).obj k)).mapIso (componentIso k))
    (by
      intro i j f
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map (smallCMInclusion D (hincl f)) ≫
          (normalSquare j).isoPullback.hom =
        (normalSquare i).isoPullback.hom ≫ ((pulledDiagram).obj.map f).left
      have hf : ((pulledDiagram).obj.map f).left ≫
          pullback.fst ((schemes).map (smallCMInclusion D (hcoeff j.unop))) π =
          pullback.fst ((schemes).map (smallCMInclusion D (hcoeff i.unop))) π ≫
            (schemes).map (smallCMInclusion D (hincl f)) := by
        exact pullback.lift_fst _ _ _
      have hs : ((pulledDiagram).obj.map f).left ≫
          pullback.snd ((schemes).map (smallCMInclusion D (hcoeff j.unop))) π =
          pullback.snd ((schemes).map (smallCMInclusion D (hcoeff i.unop))) π := by
        exact pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc, (normalSquare j).isoPullback_hom_fst,
          Category.assoc, hf, ← Category.assoc, (normalSquare i).isoPullback_hom_fst]
        exact (fieldProjection).naturality (smallCMInclusion D (hincl f))
      · rw [Category.assoc, (normalSquare j).isoPullback_hom_snd,
          Category.assoc, hs, (normalSquare i).isoPullback_hom_snd]
        exact (projection).naturality f |>.trans (Category.comp_id _))

local notation "towerIso" => cmHarrisGeometricCoefficientEtaleTowerPullbackIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

/-- The full exact geometric coefficient-cover diagram is canonically isomorphic
to the arbitrary-base-change pullback of the full original diagram. -/
def cmHarrisGeometricCoefficientEtaleDiagramPullbackIso :
    etaleDiagram ≅ pulledDiagram where
  hom :=
    { hom := (towerIso).hom
      comm k g := (componentIso k).hom.comm g }
  inv :=
    { hom := (towerIso).inv
      comm k g := (componentIso k).inv.comm g }
  hom_inv_id := by
    apply EquivariantDiagram.Hom.ext
    exact (towerIso).hom_inv_id
  inv_hom_id := by
    apply EquivariantDiagram.Hom.ext
    exact (towerIso).inv_hom_id

local notation "diagramIso" => cmHarrisGeometricCoefficientEtaleDiagramPullbackIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

/-- The full diagram comparison retains the exact original cartesian comparison maps. -/
@[simp] theorem cmHarrisGeometricCoefficientEtaleDiagramPullbackIso_hom_app_left
    (k : ℕᵒᵖ) :
    (((diagramIso).hom.hom.app k).left) = (normalSquare k).isoPullback.hom := rfl

@[simp] theorem cmHarrisGeometricCoefficientEtaleDiagramPullbackIso_inv_app_left
    (k : ℕᵒᵖ) :
    (((diagramIso).inv.hom.app k).left) = (normalSquare k).isoPullback.inv := rfl

/-- Its first coordinate is the existing geometric projection at the same fine level. -/
@[reassoc (attr := simp)]
theorem cmHarrisGeometricCoefficientEtaleDiagramPullbackIso_hom_app_fst (k : ℕᵒᵖ) :
    ((diagramIso).hom.hom.app k).left ≫
        pullback.fst ((schemes).map (smallCMInclusion D (hcoeff k.unop))) π =
      (fieldProjection).app (Vcoeff k.unop) :=
  (normalSquare k).isoPullback_hom_fst

/-- Its second coordinate is the exact coarse geometric coefficient projection. -/
@[reassoc (attr := simp)]
theorem cmHarrisGeometricCoefficientEtaleDiagramPullbackIso_hom_app_snd (k : ℕᵒᵖ) :
    ((diagramIso).hom.hom.app k).left ≫
        pullback.snd ((schemes).map (smallCMInclusion D (hcoeff k.unop))) π =
      (projection).app k :=
  (normalSquare k).isoPullback_hom_snd

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
