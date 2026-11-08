import Langlands.Shimura.PEL.HarrisTaylorCMGeometricUpperPair
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricPairCoherence

/-! # Original upper-pair inverse image and three-level CM coherence -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Cohomology
open Langlands.Geometry Langlands.Geometry.EtaleInverseImage

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

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor T.obj)

variable (hRigidV : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor V.obj)

local notation "hTU" => hTV.trans hVU
local notation "XT" => (geometricSchemes).obj T
local notation "XV" => (geometricSchemes).obj V
local notation "J" => Scheme.smallEtaleTopology XT
local notation "R" => HarrisCoefficientIntegers K p
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hTV)
local notation "pullSystems" => (Functor.whiskeringRight ℕᵒᵖ _ _).obj (inverseImage coarseMap R)
local notation "commonChain" => cmHarrisGeometricTripleCommonSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "association" => cmHarrisGeometricTripleCommonAssociation D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "separateChain" => cmHarrisGeometricTripleSeparateSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "originalPairChain" => cmHarrisGeometricTripleOriginalPairSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "tripleMiddleIso" => cmHarrisGeometricTripleMiddleCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "tripleUpperIso" => cmHarrisGeometricTripleUpperCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "pairOwnIso" => cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairOriginalIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairInclusion" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairOwnSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V ρ p m hm existence geometry hRigidV
local notation "pairOriginalSystem" => cmHarrisGeometricCoarseAssociatedSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "ownInverseIso" => cmHarrisGeometricTripleUpperPairOwnInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "originalInverseIso" => cmHarrisGeometricTripleUpperPairOriginalInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "lowerComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "directComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "upperInclusion" => cmHarrisTripleUpperCoefficientInclusion D ρ p U V T hVU hTV m hm

/-- Pull back the original separate V system, then use the constructed actual cover comparisons. -/
def cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso :
    pairOwnSystem ⋙ inverseImage coarseMap R ≅ (separateChain).obj' 1 :=
  (pullSystems).mapIso pairOwnIso ≪≫ ownInverseIso ≪≫ (tripleMiddleIso).symm

/-- Pull back the original separate coarse U system, preserving its original cover and coefficients. -/
def cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso :
    pairOriginalSystem ⋙ inverseImage coarseMap R ≅ (separateChain).obj' 2 :=
  (pullSystems).mapIso pairOriginalIso ≪≫ originalInverseIso ≪≫ (tripleUpperIso).symm

local notation "ownSeparateIso" => cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "originalSeparateIso" => cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- Inverse image of the original named upper-pair map has its original common-cover normalization. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairOriginalInverse_common :
    (pullSystems).map pairComparison ≫
        (pullSystems).map (pairOriginalIso).hom ≫ (originalInverseIso).hom =
      ((pullSystems).map (pairOwnIso).hom ≫ (ownInverseIso).hom) ≫
        (association).map upperInclusion := by
  have hc : pairComparison ≫ (pairOriginalIso).hom =
      (pairOwnIso).hom ≫ pairInclusion :=
    cmHarrisGeometricLatticeCoefficientComparison_common D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
  rw [← Category.assoc, ← (pullSystems).map_comp, hc, (pullSystems).map_comp,
    Category.assoc]
  have hs : (pullSystems).map pairInclusion ≫ (originalInverseIso).hom =
      (ownInverseIso).hom ≫ (association).map upperInclusion :=
    cmHarrisGeometricTripleUpperPairInverseInclusion_square D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
  rw [hs, ← Category.assoc]

/-- The actual inverse image of the original upper-pair comparison is the existing triple upper leg. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairOriginalInverse_square :
    (pullSystems).map pairComparison ≫ (originalSeparateIso).hom =
      (ownSeparateIso).hom ≫ (separateChain).map' 1 2 := by
  apply (cancel_mono (tripleUpperIso).hom).1
  change ((pullSystems).map pairComparison ≫
      ((pullSystems).map (pairOriginalIso).hom ≫ (originalInverseIso).hom ≫
        (tripleUpperIso).inv)) ≫ (tripleUpperIso).hom =
    (((pullSystems).map (pairOwnIso).hom ≫ (ownInverseIso).hom ≫
        (tripleMiddleIso).inv) ≫
      ((tripleMiddleIso).hom ≫ (commonChain).map' 1 2 ≫ (tripleUpperIso).inv)) ≫
        (tripleUpperIso).hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change (pullSystems).map pairComparison ≫
      (pullSystems).map (pairOriginalIso).hom ≫ (originalInverseIso).hom =
    (pullSystems).map (pairOwnIso).hom ≫ (ownInverseIso).hom ≫
      (association).map upperInclusion
  simpa only [Category.assoc] using
    (cmHarrisGeometricTripleUpperPairOriginalInverse_common D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV)

/-- Transport only the endpoints of genuine inverse image of the original named upper-pair map. -/
def cmHarrisGeometricTripleUpperPairOriginalInverseComparison :
    (separateChain).obj' 1 ⟶ (separateChain).obj' 2 :=
  (ownSeparateIso).inv ≫ (pullSystems).map pairComparison ≫ (originalSeparateIso).hom

local notation "inverseComparison" => cmHarrisGeometricTripleUpperPairOriginalInverseComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- This constructed map equals the previously constructed separate triple upper leg. -/
@[simp] theorem cmHarrisGeometricTripleUpperPairOriginalInverseComparison_eq_separate :
    inverseComparison = (separateChain).map' 1 2 := by
  change (ownSeparateIso).inv ≫ (pullSystems).map pairComparison ≫
    (originalSeparateIso).hom = _
  rw [cmHarrisGeometricTripleUpperPairOriginalInverse_square]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The original direct pair map factors through the original lower pair and this genuine inverse image. -/
@[reassoc] theorem cmHarrisGeometricTripleOriginalPairInverseImage_coherence :
    directComparison = lowerComparison ≫ inverseComparison := by
  rw [cmHarrisGeometricTripleUpperPairOriginalInverseComparison_eq_separate]
  exact (cmHarrisGeometricTripleOriginalPairSystemChain_hom D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid).symm

/-- The factorization explicitly retains the original inverse-image functor and both constructed endpoints. -/
@[reassoc] theorem cmHarrisGeometricTripleOriginalPairInverseImage_coherence_explicit :
    directComparison = lowerComparison ≫ (ownSeparateIso).inv ≫
      Functor.whiskerRight pairComparison (inverseImage coarseMap R) ≫
        (originalSeparateIso).hom := by
  change directComparison = lowerComparison ≫ (ownSeparateIso).inv ≫
    (pullSystems).map pairComparison ≫ (originalSeparateIso).hom
  have hc := cmHarrisGeometricTripleOriginalPairInverseImage_coherence D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
  change directComparison = lowerComparison ≫ ((ownSeparateIso).inv ≫
    (pullSystems).map pairComparison ≫ (originalSeparateIso).hom) at hc
  simpa only [Category.assoc] using hc

/-- The original lower pair map and actual inverse image of the original upper pair form one chain. -/
def cmHarrisGeometricTripleOriginalInverseImageSystemChain :
    ComposableArrows (ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R)) 2 :=
  ComposableArrows.mk₂ lowerComparison inverseComparison

local notation "inverseChain" => cmHarrisGeometricTripleOriginalInverseImageSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- The chain built using the genuine upper inverse image equals the existing original-pair chain. -/
@[simp] theorem cmHarrisGeometricTripleOriginalInverseImageSystemChain_eq_original :
    inverseChain = originalPairChain := by
  change ComposableArrows.mk₂ lowerComparison inverseComparison = originalPairChain
  rw [cmHarrisGeometricTripleUpperPairOriginalInverseComparison_eq_separate]
  rfl

/-- The same actual three coefficient systems have their original common-cover chain isomorphism. -/
def cmHarrisGeometricTripleOriginalInverseImageChainIso : inverseChain ≅ commonChain :=
  eqToIso (cmHarrisGeometricTripleOriginalInverseImageSystemChain_eq_original D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV) ≪≫
    cmHarrisGeometricTripleOriginalPairChainIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- The inverse endpoint isomorphisms preserve every original inverse-image exponent map. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((separateChain).obj' 1).map f ≫ (ownSeparateIso).inv.app j =
      (ownSeparateIso).inv.app i ≫ (inverseImage coarseMap R).map ((pairOwnSystem).map f) :=
  (ownSeparateIso).inv.naturality f

@[reassoc] theorem cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((separateChain).obj' 2).map f ≫ (originalSeparateIso).inv.app j =
      (originalSeparateIso).inv.app i ≫
        (inverseImage coarseMap R).map ((pairOriginalSystem).map f) :=
  (originalSeparateIso).inv.naturality f

/-- Both legs and the composite retain every original exponent reduction, including zero. -/
@[reassoc] theorem cmHarrisGeometricTripleOriginalInverseImageSystemChain_transition
    {a b : Fin 3} (g : a ⟶ b) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((inverseChain).obj a).map f ≫ ((inverseChain).map g).app j =
      ((inverseChain).map g).app i ≫ ((inverseChain).obj b).map f :=
  ((inverseChain).map g).naturality f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
