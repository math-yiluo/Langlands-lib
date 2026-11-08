import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeInverseImage
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricUpperPairOwnEndpoint
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricUpperPairOriginalEndpoint
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseTowerCoherence

/-! # Composition of the original own-system CM lattice inverse-image morphisms -/

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

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
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

variable (hRigidU : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "hTU" => hTV.trans hVU
local notation "XT" => (geometricSchemes).obj T
local notation "J" => Scheme.smallEtaleTopology XT
local notation "R" => HarrisCoefficientIntegers K p
local notation "mapVU" => (geometricSchemes).map (smallCMInclusion D hVU)
local notation "mapTV" => (geometricSchemes).map (smallCMInclusion D hTV)
local notation "mapTU" => (geometricSchemes).map (smallCMInclusion D hTU)
local notation "baseEq" => cmHarrisGeometricCoarseTowerBaseMap_comp D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
local notation "systemU" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigidU
local notation "systemV" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V ρ p m hm existence geometry hRigidV
local notation "systemT" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q T ρ p m hm existence geometry hRigid
local notation "directV" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV hRigidU
local notation "directT" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU
local notation "lowerIso" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid hRigidV
local notation "upperComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "lowerComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "directComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "upperDelta" => cmHarrisGeometricLatticeInverseImageComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV hRigidU
local notation "lowerDelta" => cmHarrisGeometricLatticeInverseImageComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid hRigidV
local notation "directDelta" => cmHarrisGeometricLatticeInverseImageComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU
local notation "towerIso" => cmHarrisGeometricCoarseTowerInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "ownCoefficients" => cmHarrisCoefficientDiagram D ρ p T m hm
local notation "coefficientInclusion" => cmHarrisLatticeCommonCoefficientInclusion D ρ p U T hTU m hm
local notation "ownCoverIso" => cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "coarseCoverIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "commonCoefficientMap" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "commonCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "commonOriginalInc" k:arg => cmHarrisGeometricLatticeCommonOriginalInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid k
local notation "ownInc" k:arg => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q T ρ p m hm existence geometry hRigid k
local notation "ownCoverMap" k:arg => cmHarrisGeometricLatticeCommonOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid k

/-- The original three lattice maps satisfy the factorization with normalized actual endpoints. -/
@[reassoc] theorem cmHarrisGeometricLatticeCoefficientComparison_inverseImage_coherence :
    directComparison = lowerComparison ≫ (lowerIso).inv ≫
      Functor.whiskerRight upperComparison (inverseImage mapTV R) ≫ (towerIso).hom := by
  have hc := cmHarrisGeometricTripleOriginalPairInverseImage_coherence_explicit D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
  rw [cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso_eq_coarse,
    cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso_eq_tower] at hc
  exact hc

/-- Compose the original lower lattice morphism with actual inverse image of the original
upper lattice morphism, then use the actual inverse-image composition and equality transport. -/
def cmHarrisGeometricLatticeIteratedInverseImageComparison :
    systemT ⟶ systemU ⋙ inverseImage mapTU R :=
  lowerDelta ≫ Functor.whiskerRight upperDelta (inverseImage mapTV R) ≫
    (Functor.associator systemU (inverseImage mapVU R) (inverseImage mapTV R)).hom ≫
    (Functor.isoWhiskerLeft systemU
      (inverseImageComp R mapVU mapTV ≪≫ inverseImageCongr R baseEq)).hom

local notation "iteratedDelta" => cmHarrisGeometricLatticeIteratedInverseImageComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU

/-- At each exponent both original lattice maps and the genuine composition comparisons remain. -/
@[simp] theorem cmHarrisGeometricLatticeIteratedInverseImageComparison_app (k : ℕᵒᵖ) :
    (iteratedDelta).app k =
      (lowerDelta).app k ≫ (inverseImage mapTV R).map ((upperDelta).app k) ≫
        (inverseImageComp R mapVU mapTV).hom.app ((systemU).obj k) ≫
        (inverseImageCongr R baseEq).hom.app ((systemU).obj k) := by
  change (lowerDelta).app k ≫ (inverseImage mapTV R).map ((upperDelta).app k) ≫
      𝟙 ((inverseImage mapTV R).obj
        ((inverseImage mapVU R).obj ((systemU).obj k))) ≫
      (inverseImageComp R mapVU mapTV).hom.app ((systemU).obj k) ≫
      (inverseImageCongr R baseEq).hom.app ((systemU).obj k) = _
  exact congrArg
    (fun a => (lowerDelta).app k ≫ (inverseImage mapTV R).map ((upperDelta).app k) ≫ a)
    (Category.id_comp
      ((inverseImageComp R mapVU mapTV).hom.app ((systemU).obj k) ≫
        (inverseImageCongr R baseEq).hom.app ((systemU).obj k)))

/-- The original direct inverse-image lattice morphism is the successive original one. -/
theorem cmHarrisGeometricLatticeIteratedInverseImageComparison_eq :
    iteratedDelta = directDelta := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono ((directT).hom.app k)).1
  rw [cmHarrisGeometricLatticeIteratedInverseImageComparison_app]
  simp only [Category.assoc]
  rw [cmHarrisGeometricCoarseTowerInverseImage_hom_comp D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU k]
  change (lowerComparison).app k ≫ (lowerIso).inv.app k ≫
      (inverseImage mapTV R).map
        ((upperComparison).app k ≫ (directV).inv.app k) ≫
      (inverseImage mapTV R).map ((directV).hom.app k) ≫ (towerIso).hom.app k =
    ((directComparison).app k ≫ (directT).inv.app k) ≫ (directT).hom.app k
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  have hc := congrArg (fun a => a.app k)
    (cmHarrisGeometricLatticeCoefficientComparison_inverseImage_coherence D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc] using hc.symm

/-- The full composition law written directly in terms of the three original morphisms. -/
theorem cmHarrisGeometricLatticeInverseImageComparison_comp :
    directDelta =
      lowerDelta ≫ Functor.whiskerRight upperDelta (inverseImage mapTV R) ≫
        (Functor.associator systemU (inverseImage mapVU R) (inverseImage mapTV R)).hom ≫
        (Functor.isoWhiskerLeft systemU
          (inverseImageComp R mapVU mapTV ≪≫ inverseImageCongr R baseEq)).hom :=
  (cmHarrisGeometricLatticeIteratedInverseImageComparison_eq D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU).symm

/-- Componentwise composition retains the original lattice maps and both genuine comparisons. -/
theorem cmHarrisGeometricLatticeInverseImageComparison_comp_app (k : ℕᵒᵖ) :
    (directDelta).app k =
      (lowerDelta).app k ≫ (inverseImage mapTV R).map ((upperDelta).app k) ≫
        (inverseImageComp R mapVU mapTV).hom.app ((systemU).obj k) ≫
        (inverseImageCongr R baseEq).hom.app ((systemU).obj k) := by
  rw [← cmHarrisGeometricLatticeIteratedInverseImageComparison_eq D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU]
  exact cmHarrisGeometricLatticeIteratedInverseImageComparison_app D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU k

/-- Every original exponent transition is compatible with the full successive morphism. -/
@[reassoc] theorem cmHarrisGeometricLatticeIteratedInverseImageComparison_transition
    {i j : ℕᵒᵖ} (u : i ⟶ j) :
    (systemT).map u ≫ (iteratedDelta).app j =
        (iteratedDelta).app i ≫ (inverseImage mapTU R).map ((systemU).map u) :=
  (iteratedDelta).naturality u

/-- The successive comparison recovers the original direct lattice morphism on the coarse cover. -/
@[reassoc] theorem cmHarrisGeometricLatticeIteratedInverseImageComparison_coarse :
    iteratedDelta ≫ (directT).hom = directComparison := by
  rw [cmHarrisGeometricLatticeIteratedInverseImageComparison_eq D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU]
  exact cmHarrisGeometricLatticeInverseImageComparison_coarse D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU

/-- On the original direct common cover the successive map is the same actual coefficient inclusion. -/
@[reassoc] theorem cmHarrisGeometricLatticeIteratedInverseImageComparison_common :
    iteratedDelta ≫ (directT).hom ≫ (coarseCoverIso).hom =
      (ownCoverIso).hom ≫ commonCoefficientMap := by
  rw [cmHarrisGeometricLatticeIteratedInverseImageComparison_eq D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU]
  exact cmHarrisGeometricLatticeInverseImageComparison_common D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU

/-- Original invariant sections retain the direct cover coordinate and original lattice inclusion. -/
@[reassoc] theorem cmHarrisGeometricLatticeIteratedInverseImageComparison_inclusion (k : ℕᵒᵖ) :
    (iteratedDelta).app k ≫ (directT).hom.app k ≫
        (coarseCoverIso).hom.app k ≫ commonOriginalInc k =
      ownInc k ≫ coverPullback J (ownCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) ≫
        (productSheaf J ((commonCovers).obj.obj k)).map
          ((constantSheaf J (ModuleCat.{0} R)).map ((coefficientInclusion).hom.app k)) := by
  rw [cmHarrisGeometricLatticeIteratedInverseImageComparison_eq D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU]
  exact cmHarrisGeometricLatticeInverseImageComparison_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU k

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
