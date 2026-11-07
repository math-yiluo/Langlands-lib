import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientTripleCommon
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficientDiagram
import Langlands.Shimura.Coefficients.VaryingCoverInverse

/-! # Actual geometric descent of the three original canonical coefficient systems -/

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

variable (U V T : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  (hTV : T.obj.subgroup ≤ V.obj.subgroup)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

local notation "levels" => cmHarrisTripleCommonLevels D ρ p U V T hVU hTV m hm
local notation "groups" => cmHarrisTripleCommonGroups D ρ p U V T hVU hTV m hm
local notation "Vcoeff" k => cmHarrisTripleCommonLevel D ρ p U V T hVU hTV m hm k
local notation "hcoeff" k => cmHarrisTripleCommonLevel_le D ρ p U V T hVU hTV m hm k
local notation "hincl" f => cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom (f).unop)
local notation "Xbar" => (geometricSchemes).obj T
local notation "geometricAction" k => cmGeometricNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q T (Vcoeff k) (hcoeff k)

/-- The actual geometric scheme tower at the intersection of all three original coefficient kernel levels,
with the original inverse-right residual actions. -/
def cmHarrisGeometricTripleCommonSchemeDiagram : EquivariantDiagram groups Scheme where
  obj := levels ⋙ geometricSchemes
  ρ k := (geometricAction k.unop).ρ
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D T (Vcoeff i.unop) (hcoeff i.unop) g) ≫
          (geometricSchemes).map (smallCMInclusion D (hincl f)) =
        (geometricSchemes).map (smallCMInclusion D (hincl f)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D T (Vcoeff j.unop) (hcoeff j.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "schemeDiagram" => cmHarrisGeometricTripleCommonSchemeDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V T hVU hTV ρ p m hm

/-- No new levels or transition maps are selected by the geometric diagram. -/
@[simp] theorem cmHarrisGeometricTripleCommonSchemeDiagram_obj :
    (schemeDiagram).obj = levels ⋙ geometricSchemes := rfl

@[simp] theorem cmHarrisGeometricTripleCommonSchemeDiagram_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (schemeDiagram).obj.map f =
      (geometricSchemes).map (smallCMInclusion D (hincl f)) := rfl

/-- All coefficient covers project to the same existing geometric coarse level. -/
def cmHarrisGeometricTripleCommonSchemeProjection :
    (schemeDiagram).obj ⟶ (Functor.const ℕᵒᵖ).obj Xbar where
  app k := (geometricSchemes).map (smallCMInclusion D (hcoeff k.unop))
  naturality i j f := by
    dsimp [cmHarrisGeometricTripleCommonSchemeDiagram, cmHarrisTripleCommonLevels]
    rw [Category.comp_id, ← (geometricSchemes).map_comp, smallCMInclusion_trans]

local notation "projection" => cmHarrisGeometricTripleCommonSchemeProjection D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V T hVU hTV ρ p m hm

/-- Every residual action fixes the exact geometric coarse projection. -/
@[reassoc] theorem cmHarrisGeometricTripleCommonSchemeProjection_invariant
    (k : ℕᵒᵖ) (g : (groups).obj k) :
    (schemeDiagram).ρ k g ≫ (projection).app k = (projection).app k :=
  cmGeometricNormalProjection_invariant D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q T (Vcoeff k.unop) (hcoeff k.unop) g

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor T.obj)

/-- The exact finite geometric torsor at the actual common coefficient kernel.
The published dominant-unramified criterion discharges that generic premise. -/
def cmHarrisGeometricTripleCommonTorsor (k : ℕ) :
    {Y : Action (Xbar).Etale (SmallCMResidualGroup D T (Vcoeff k)) //
      IsFiniteGeometricTorsor Xbar Y} :=
  cmGeometricNormalGeometricTorsor_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q T (Vcoeff k)
    (hcoeff k) existence geometry hRigid
    DominantUnramifiedEtaleProof.dominantUnramifiedEtale

local notation "torsor" k => cmHarrisGeometricTripleCommonTorsor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm
  existence geometry hRigid k

/-- The exact common-kernel covers and original forgetting maps in the
small-etale category of the same geometric coarse level. -/
def cmHarrisGeometricTripleCommonEtaleTower : ℕᵒᵖ ⥤ (Xbar).Etale where
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

local notation "etaleTower" => cmHarrisGeometricTripleCommonEtaleTower D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm
  existence geometry hRigid

/-- The exact geometric coefficient torsors form a varying-group equivariant diagram. -/
def cmHarrisGeometricTripleCommonEtaleDiagram : EquivariantDiagram groups (Xbar).Etale where
  obj := etaleTower
  ρ k := (torsor k.unop).val.ρ
  comm f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).comm f g

local notation "etaleDiagram" => cmHarrisGeometricTripleCommonEtaleDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V T hVU hTV ρ p m hm existence geometry hRigid

@[simp] theorem cmHarrisGeometricTripleCommonEtaleDiagram_action (k : ℕᵒᵖ) :
    (etaleDiagram).action k = (torsor k.unop).val := rfl

@[simp] theorem cmHarrisGeometricTripleCommonEtaleDiagram_obj_left (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).left = (geometricSchemes).obj (Vcoeff k.unop) := rfl

@[simp] theorem cmHarrisGeometricTripleCommonEtaleDiagram_obj_hom (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).hom = (projection).app k := rfl

@[simp] theorem cmHarrisGeometricTripleCommonEtaleDiagram_map_left
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((etaleDiagram).obj.map f).left =
      (geometricSchemes).map (smallCMInclusion D (hincl f)) := rfl

/-- Each deck transformation is the existing inverse-right geometric tower map. -/
@[simp] theorem cmHarrisGeometricTripleCommonEtaleDiagram_action_mk_left
    (k : ℕᵒᵖ) (g : T.obj.subgroup) :
    ((etaleDiagram).ρ k (QuotientGroup.mk g)).left =
      (geometricSchemes).map
        (smallCMNormalInverseArrow D T (Vcoeff k.unop) (hcoeff k.unop) g) := rfl

/-- The finite geometric torsor condition is proved for every exact component. -/
theorem cmHarrisGeometricTripleCommonEtaleDiagram_isFiniteGeometricTorsor (k : ℕᵒᵖ) :
    IsFiniteGeometricTorsor Xbar ((etaleDiagram).action k) :=
  (torsor k.unop).property

/-- Each exact geometric common-kernel cover covers the final object of its small-etale site. -/
theorem cmHarrisGeometricTripleCommonEtaleDiagram_coversTop (k : ℕᵒᵖ) :
    (Scheme.smallEtaleTopology Xbar).CoversTop
      (fun _ : Unit => (etaleDiagram).obj.obj k) :=
  etale_coversTop_of_surjective (torsor k.unop).val.V (torsor k.unop).property.2.2.1

local notation "torsorProperty" =>
  cmHarrisGeometricTripleCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm
    existence geometry hRigid
local notation "J" => Scheme.smallEtaleTopology Xbar
local notation "R" => HarrisCoefficientIntegers K p
local notation "ownCoefficients" => cmHarrisTripleOwnCoefficients D ρ p U V T hVU hTV m hm
local notation "middleCoefficients" => cmHarrisTripleMiddleCoefficients D ρ p U V T hVU hTV m hm
local notation "upperCoefficients" => cmHarrisTripleUpperCoefficients D ρ p U V T hVU hTV m hm
local notation "coefficientChain" => cmHarrisTripleCoefficientChain D ρ p U V T hVU hTV m hm
local notation "lowerCoefficient" => cmHarrisTripleLowerCoefficientInclusion D ρ p U V T hVU hTV m hm
local notation "upperCoefficient" => cmHarrisTripleUpperCoefficientInclusion D ρ p U V T hVU hTV m hm
local notation "directCoefficient" => cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm

/-- Association on the actual simultaneous-kernel CM covers, retaining complete coefficient diagrams. -/
def cmHarrisGeometricTripleCommonAssociation :
    EquivariantDiagram groups (ModuleCat.{0} R) ⥤
      (ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R)) :=
  etaleAssociatedVaryingSystemFunctor Xbar etaleDiagram torsorProperty

local notation "association" => cmHarrisGeometricTripleCommonAssociation D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm
  existence geometry hRigid

/-- The actual three-level coefficient chain associated on the same geometric common-kernel covers. -/
def cmHarrisGeometricTripleCommonSystemChain :
    ComposableArrows (ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R)) 2 :=
  coefficientChain ⋙ association

local notation "systemChain" => cmHarrisGeometricTripleCommonSystemChain D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm
  existence geometry hRigid

/-- The source is association of the full original T-lattice coefficient system. -/
@[simp] theorem cmHarrisGeometricTripleCommonSystemChain_own :
    (systemChain).obj' 0 = (association).obj ownCoefficients := rfl

/-- The middle is association of the original V-lattice coefficient system restricted to T. -/
@[simp] theorem cmHarrisGeometricTripleCommonSystemChain_middle :
    (systemChain).obj' 1 = (association).obj middleCoefficients := rfl

/-- The target is association of the original U-lattice coefficient system restricted to T. -/
@[simp] theorem cmHarrisGeometricTripleCommonSystemChain_upper :
    (systemChain).obj' 2 = (association).obj upperCoefficients := rfl

/-- The lower arrow descends the original T-to-V lattice map. -/
@[simp] theorem cmHarrisGeometricTripleCommonSystemChain_lower :
    (systemChain).map' 0 1 = (association).map lowerCoefficient := rfl

/-- The upper arrow descends the original V-to-U lattice map restricted to T. -/
@[simp] theorem cmHarrisGeometricTripleCommonSystemChain_upper_map :
    (systemChain).map' 1 2 = (association).map upperCoefficient := rfl

/-- The full composite descends exactly the original direct T-to-U coefficient inclusion. -/
@[simp] theorem cmHarrisGeometricTripleCommonSystemChain_hom :
    (systemChain).hom = (association).map directCoefficient := by
  change (association).map (coefficientChain).hom = _
  rw [cmHarrisTripleCoefficientChain_hom]

/-- The two descended original coefficient maps compose to the descended direct original map. -/
@[reassoc] theorem cmHarrisGeometricTripleCommonSystemChain_comp :
    (association).map lowerCoefficient ≫ (association).map upperCoefficient =
      (association).map directCoefficient := by
  rw [← (association).map_comp, cmHarrisTripleCoefficientInclusion_comp]

/-- Every component of every arrow is association of the corresponding original equivariant map. -/
@[simp] theorem cmHarrisGeometricTripleCommonSystemChain_map_app
    {a b : Fin 3} (g : a ⟶ b) (k : ℕᵒᵖ) :
    ((systemChain).map g).app k =
      (etaleAssociatedFunctor Xbar ((etaleDiagram).action k)).map
        ((EquivariantDiagram.evaluation k).map ((coefficientChain).map g)) := rfl

/-- All original exponent reductions commute with each arrow of the descended chain. -/
@[reassoc] theorem cmHarrisGeometricTripleCommonSystemChain_transition
    {a b : Fin 3} (g : a ⟶ b) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((systemChain).obj a).map f ≫ ((systemChain).map g).app j =
      ((systemChain).map g).app i ≫ ((systemChain).obj b).map f :=
  ((systemChain).map g).naturality f

/-- Invariant sections of each original coefficient system on the exact common cover. -/
def cmHarrisGeometricTripleCommonSystemInclusion (a : Fin 3) (k : ℕᵒᵖ) :
    ((systemChain).obj a).obj k ⟶ (productSheaf J ((etaleDiagram).obj.obj k)).obj
      ((constantSheaf J (ModuleCat.{0} R)).obj (((coefficientChain).obj a).obj.obj k)) :=
  etaleAssociatedInclusion Xbar ((etaleDiagram).action k) (((coefficientChain).obj a).action k)

local notation "sectionInclusion" a:arg k:arg =>
  cmHarrisGeometricTripleCommonSystemInclusion D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm
    existence geometry hRigid a k

instance cmHarrisGeometricTripleCommonSystemInclusion_mono (a : Fin 3) (k : ℕᵒᵖ) :
    Mono (sectionInclusion a k) :=
  etaleAssociatedInclusion_mono Xbar ((etaleDiagram).action k)
    (((coefficientChain).obj a).action k)

/-- The original coefficient reductions characterize every descended exponent transition. -/
@[reassoc] theorem cmHarrisGeometricTripleCommonSystemChain_map_inclusion
    (a : Fin 3) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((systemChain).obj a).map f ≫ sectionInclusion a j ≫
        coverPullback J ((etaleDiagram).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj (((coefficientChain).obj a).obj.obj j)) =
      sectionInclusion a i ≫ (productSheaf J ((etaleDiagram).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (((coefficientChain).obj a).obj.map f)) :=
  etaleAssociatedTransition_inclusion Xbar etaleDiagram torsorProperty f ((coefficientChain).obj a)

/-- On actual invariant sections every descended chain arrow applies its original coefficient map. -/
@[reassoc] theorem cmHarrisGeometricTripleCommonSystemChain_inclusion
    {a b : Fin 3} (g : a ⟶ b) (k : ℕᵒᵖ) :
    ((systemChain).map g).app k ≫ sectionInclusion b k =
      sectionInclusion a k ≫ (productSheaf J ((etaleDiagram).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (((coefficientChain).map g).hom.app k)) :=
  etaleAssociatedInclusion_natural Xbar ((etaleDiagram).action k)
    ((EquivariantDiagram.evaluation k).map ((coefficientChain).map g))

/-- The full composite on invariant sections is the actual direct included-vector coefficient map. -/
@[reassoc] theorem cmHarrisGeometricTripleCommonSystemChain_hom_inclusion (k : ℕᵒᵖ) :
    (systemChain).hom.app k ≫ sectionInclusion 2 k =
      sectionInclusion 0 k ≫ (productSheaf J ((etaleDiagram).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((directCoefficient).hom.app k)) := by
  change ((association).map (coefficientChain).hom).app k ≫ _ = _
  rw [cmHarrisTripleCoefficientChain_hom]
  exact etaleAssociatedInclusion_natural Xbar ((etaleDiagram).action k)
    ((EquivariantDiagram.evaluation k).map directCoefficient)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
