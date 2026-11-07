import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientLatticeComparison
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficientDiagram
import Langlands.Shimura.Coefficients.VaryingCoverInverse

/-! # Actual geometric common-kernel descent of the canonical lattice comparison -/

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

local notation "levels" => cmHarrisLatticeCommonLevels D ρ p U V hVU m hm
local notation "groups" => cmHarrisLatticeCommonGroups D ρ p U V hVU m hm
local notation "Vcoeff" k => cmHarrisLatticeCommonLevel D ρ p U V hVU m hm k
local notation "hcoeff" k => cmHarrisLatticeCommonLevel_le D ρ p U V hVU m hm k
local notation "hincl" f => cmHarrisLatticeCommonLevel_antitone D ρ p U V hVU m hm (leOfHom (f).unop)
local notation "Xbar" => (geometricSchemes).obj V
local notation "geometricAction" k => cmGeometricNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q V (Vcoeff k) (hcoeff k)

/-- The actual geometric scheme tower at the intersection of the two original coefficient kernel levels,
with the original inverse-right residual actions. -/
def cmHarrisGeometricLatticeCommonSchemeDiagram : EquivariantDiagram groups Scheme where
  obj := levels ⋙ geometricSchemes
  ρ k := (geometricAction k.unop).ρ
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D V (Vcoeff i.unop) (hcoeff i.unop) g) ≫
          (geometricSchemes).map (smallCMInclusion D (hincl f)) =
        (geometricSchemes).map (smallCMInclusion D (hincl f)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D V (Vcoeff j.unop) (hcoeff j.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "schemeDiagram" => cmHarrisGeometricLatticeCommonSchemeDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU ρ p m hm

/-- No new levels or transition maps are selected by the geometric diagram. -/
@[simp] theorem cmHarrisGeometricLatticeCommonSchemeDiagram_obj :
    (schemeDiagram).obj = levels ⋙ geometricSchemes := rfl

@[simp] theorem cmHarrisGeometricLatticeCommonSchemeDiagram_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (schemeDiagram).obj.map f =
      (geometricSchemes).map (smallCMInclusion D (hincl f)) := rfl

/-- All coefficient covers project to the same existing geometric coarse level. -/
def cmHarrisGeometricLatticeCommonSchemeProjection :
    (schemeDiagram).obj ⟶ (Functor.const ℕᵒᵖ).obj Xbar where
  app k := (geometricSchemes).map (smallCMInclusion D (hcoeff k.unop))
  naturality i j f := by
    dsimp [cmHarrisGeometricLatticeCommonSchemeDiagram, cmHarrisLatticeCommonLevels]
    rw [Category.comp_id, ← (geometricSchemes).map_comp, smallCMInclusion_trans]

local notation "projection" => cmHarrisGeometricLatticeCommonSchemeProjection D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU ρ p m hm

/-- Every residual action fixes the exact geometric coarse projection. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonSchemeProjection_invariant
    (k : ℕᵒᵖ) (g : (groups).obj k) :
    (schemeDiagram).ρ k g ≫ (projection).app k = (projection).app k :=
  cmGeometricNormalProjection_invariant D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q V (Vcoeff k.unop) (hcoeff k.unop) g

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor V.obj)

/-- The exact finite geometric torsor at the actual common coefficient kernel.
The published dominant-unramified criterion discharges that generic premise. -/
def cmHarrisGeometricLatticeCommonTorsor (k : ℕ) :
    {Y : Action (Xbar).Etale (SmallCMResidualGroup D V (Vcoeff k)) //
      IsFiniteGeometricTorsor Xbar Y} :=
  cmGeometricNormalGeometricTorsor_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q V (Vcoeff k)
    (hcoeff k) existence geometry hRigid
    DominantUnramifiedEtaleProof.dominantUnramifiedEtale

local notation "torsor" k => cmHarrisGeometricLatticeCommonTorsor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigid k

/-- The exact common-kernel covers and original forgetting maps in the
small-etale category of the same geometric coarse level. -/
def cmHarrisGeometricLatticeCommonEtaleTower : ℕᵒᵖ ⥤ (Xbar).Etale where
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

local notation "etaleTower" => cmHarrisGeometricLatticeCommonEtaleTower D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigid

/-- The exact geometric coefficient torsors form a varying-group equivariant diagram. -/
def cmHarrisGeometricLatticeCommonEtaleDiagram : EquivariantDiagram groups (Xbar).Etale where
  obj := etaleTower
  ρ k := (torsor k.unop).val.ρ
  comm f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).comm f g

local notation "etaleDiagram" => cmHarrisGeometricLatticeCommonEtaleDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU ρ p m hm existence geometry hRigid

@[simp] theorem cmHarrisGeometricLatticeCommonEtaleDiagram_action (k : ℕᵒᵖ) :
    (etaleDiagram).action k = (torsor k.unop).val := rfl

@[simp] theorem cmHarrisGeometricLatticeCommonEtaleDiagram_obj_left (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).left = (geometricSchemes).obj (Vcoeff k.unop) := rfl

@[simp] theorem cmHarrisGeometricLatticeCommonEtaleDiagram_obj_hom (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).hom = (projection).app k := rfl

@[simp] theorem cmHarrisGeometricLatticeCommonEtaleDiagram_map_left
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((etaleDiagram).obj.map f).left =
      (geometricSchemes).map (smallCMInclusion D (hincl f)) := rfl

/-- Each deck transformation is the existing inverse-right geometric tower map. -/
@[simp] theorem cmHarrisGeometricLatticeCommonEtaleDiagram_action_mk_left
    (k : ℕᵒᵖ) (g : V.obj.subgroup) :
    ((etaleDiagram).ρ k (QuotientGroup.mk g)).left =
      (geometricSchemes).map
        (smallCMNormalInverseArrow D V (Vcoeff k.unop) (hcoeff k.unop) g) := rfl

/-- The finite geometric torsor condition is proved for every exact component. -/
theorem cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor (k : ℕᵒᵖ) :
    IsFiniteGeometricTorsor Xbar ((etaleDiagram).action k) :=
  (torsor k.unop).property

/-- Each exact geometric common-kernel cover covers the final object of its small-etale site. -/
theorem cmHarrisGeometricLatticeCommonEtaleDiagram_coversTop (k : ℕᵒᵖ) :
    (Scheme.smallEtaleTopology Xbar).CoversTop
      (fun _ : Unit => (etaleDiagram).obj.obj k) :=
  etale_coversTop_of_surjective (torsor k.unop).val.V (torsor k.unop).property.2.2.1

local notation "torsorProperty" =>
  cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
    existence geometry hRigid
local notation "J" => Scheme.smallEtaleTopology Xbar
local notation "R" => HarrisCoefficientIntegers K p
local notation "ownCoefficients" => cmHarrisLatticeCommonOwnCoefficients D ρ p U V hVU m hm
local notation "originalCoefficients" =>
  cmHarrisLatticeCommonOriginalCoefficients D ρ p U V hVU m hm
local notation "coefficientInclusion" =>
  cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm

/-- Association on the actual common-kernel CM covers, retaining full coefficient diagrams. -/
def cmHarrisGeometricLatticeCommonAssociation :
    EquivariantDiagram groups (ModuleCat.{0} R) ⥤
      (ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R)) :=
  etaleAssociatedVaryingSystemFunctor Xbar etaleDiagram torsorProperty

local notation "association" => cmHarrisGeometricLatticeCommonAssociation D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigid

/-- The independently constructed V lattice descended on the actual common-kernel covers. -/
def cmHarrisGeometricLatticeCommonOwnSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  (association).obj ownCoefficients

/-- The original U lattice, restricted to V, descended on the same actual covers. -/
def cmHarrisGeometricLatticeCommonOriginalSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  (association).obj originalCoefficients

local notation "ownSystem" => cmHarrisGeometricLatticeCommonOwnSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigid
local notation "originalSystem" => cmHarrisGeometricLatticeCommonOriginalSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigid

/-- The geometric comparison is the descended actual canonical-lattice inclusion. -/
def cmHarrisGeometricLatticeCommonCoefficientInclusion : ownSystem ⟶ originalSystem :=
  (association).map coefficientInclusion

local notation "geometricInclusion" =>
  cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
    existence geometry hRigid

/-- Its components use the original equivariant linear inclusion on the named covers. -/
@[simp] theorem cmHarrisGeometricLatticeCommonCoefficientInclusion_app (k : ℕᵒᵖ) :
    (geometricInclusion).app k =
      (etaleAssociatedFunctor Xbar ((etaleDiagram).action k)).map
        ((EquivariantDiagram.evaluation k).map coefficientInclusion) := rfl

/-- All descended original exponent reductions commute with the lattice comparison. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonCoefficientInclusion_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownSystem).map f ≫ (geometricInclusion).app j =
      (geometricInclusion).app i ≫ (originalSystem).map f :=
  (geometricInclusion).naturality f

/-- Inclusion of V-lattice invariant sections on the exact common-kernel cover. -/
def cmHarrisGeometricLatticeCommonOwnInclusion (k : ℕᵒᵖ) :
    (ownSystem).obj k ⟶ (productSheaf J ((etaleDiagram).obj.obj k)).obj
      ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) :=
  etaleAssociatedInclusion Xbar ((etaleDiagram).action k) ((ownCoefficients).action k)

/-- Inclusion of original U-lattice invariant sections on the same cover. -/
def cmHarrisGeometricLatticeCommonOriginalInclusion (k : ℕᵒᵖ) :
    (originalSystem).obj k ⟶ (productSheaf J ((etaleDiagram).obj.obj k)).obj
      ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) :=
  etaleAssociatedInclusion Xbar ((etaleDiagram).action k) ((originalCoefficients).action k)

local notation "ownInc" k:arg => cmHarrisGeometricLatticeCommonOwnInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigid k
local notation "originalInc" k:arg =>
  cmHarrisGeometricLatticeCommonOriginalInclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
    existence geometry hRigid k

instance cmHarrisGeometricLatticeCommonOwnInclusion_mono (k : ℕᵒᵖ) : Mono (ownInc k) :=
  etaleAssociatedInclusion_mono Xbar ((etaleDiagram).action k) ((ownCoefficients).action k)

instance cmHarrisGeometricLatticeCommonOriginalInclusion_mono (k : ℕᵒᵖ) :
    Mono (originalInc k) :=
  etaleAssociatedInclusion_mono Xbar ((etaleDiagram).action k) ((originalCoefficients).action k)

/-- Original V-lattice reductions characterize the descended transitions on actual sections. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonOwnSystem_map_inclusion
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownSystem).map f ≫ ownInc j ≫ coverPullback J ((etaleDiagram).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) =
      ownInc i ≫ (productSheaf J ((etaleDiagram).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((ownCoefficients).obj.map f)) :=
  etaleAssociatedTransition_inclusion Xbar etaleDiagram torsorProperty f ownCoefficients

/-- The original U-lattice reductions characterize their descended transitions as well. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonOriginalSystem_map_inclusion
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (originalSystem).map f ≫ originalInc j ≫ coverPullback J ((etaleDiagram).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) =
      originalInc i ≫ (productSheaf J ((etaleDiagram).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((originalCoefficients).obj.map f)) :=
  etaleAssociatedTransition_inclusion Xbar etaleDiagram torsorProperty f originalCoefficients

/-- On actual invariant sections the comparison applies the same original lattice inclusion. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonCoefficientInclusion_inclusion (k : ℕᵒᵖ) :
    (geometricInclusion).app k ≫ originalInc k =
      ownInc k ≫ (productSheaf J ((etaleDiagram).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((coefficientInclusion).hom.app k)) :=
  etaleAssociatedInclusion_natural Xbar ((etaleDiagram).action k)
    ((EquivariantDiagram.evaluation k).map coefficientInclusion)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
