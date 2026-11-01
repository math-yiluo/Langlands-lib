import Langlands.Shimura.PEL.HarrisTaylorCMKernelSchemeIsomorphism
import Langlands.Shimura.PEL.HarrisTaylorCMNormalFiniteness
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Original CM unramifiedness and finite-etale self-pullback -/

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

local notation "copies" => representedCMNormalCopies D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelPair" => representedCMNormalKernelPair D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "componentLift" => representedCMNormalKernelComponentLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "Rigid" => CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "graph" => representedCMNormalGraph D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelSection" => representedCMNormalKernelSection D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The original graph is an open immersion as an original coproduct summand
followed by the proved original kernel comparison isomorphism. -/
theorem representedCMNormalGraph_isOpenImmersion_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) (g : SmallCMResidualGroup D U V) :
    IsOpenImmersion (graph R U V hVU g) := by
  have : IsIso (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_isIso_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid
  rw [← representedCMNormalKernelComparison_ι]
  infer_instance

/-- The original forgetting diagonal is exactly the original identity graph,
hence is an open immersion without an original etaleness premise. -/
theorem representedCMNormalProjection_diagonal_isOpenImmersion_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    IsOpenImmersion (pullback.diagonal (projection R U V hVU)) := by
  have hg := representedCMNormalGraph_isOpenImmersion_of_dualGeometry D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry hRigid 1
  have he : graph R U V hVU 1 = pullback.diagonal (projection R U V hVU) :=
    representedCMNormalGraph_one D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor R U V hVU
  exact he ▸ hg

/-- The proved actual diagonal immersion gives formal unramifiedness of the
identical original projection. -/
theorem representedCMNormalProjection_formallyUnramified_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    FormallyUnramified (projection R U V hVU) := by
  have : IsOpenImmersion (pullback.diagonal (projection R U V hVU)) :=
    representedCMNormalProjection_diagonal_isOpenImmersion_of_dualGeometry D C
      preservation composition unitCoherence associativity comparison symmetry
      stability square universality dualityNaturality polarizationStability
      compatibility h htor R U V hVU existence geometry hRigid
  infer_instance

/-- The original projection's actual self-pullback is etale: under the
original comparison it is the coproduct fold of identity morphisms. -/
theorem representedCMNormalSelfPullback_etale_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    Etale (pullback.fst (projection R U V hVU) (projection R U V hVU)) := by
  have : IsIso (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_isIso_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid
  have hf : Etale (kernelComparison R U V hVU ≫
      pullback.fst (projection R U V hVU) (projection R U V hVU)) := by
    rw [representedCMNormalKernelComparison_fst]
    exact IsZariskiLocalAtSource.sigmaDesc (fun _ => by infer_instance)
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
    (kernelComparison R U V hVU) _).mp hf

/-- The actual original self-pullback as an object of the existing
finite-etale cover category over the original fine scheme. -/
def representedCMNormalSelfPullbackFiniteEtale
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    Cover ((schemes R).obj V) := by
  have : IsFinite (projection R U V hVU) :=
    representedCMNormalProjection_isFinite_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry
  have : Etale (pullback.fst (projection R U V hVU) (projection R U V hVU)) :=
    representedCMNormalSelfPullback_etale_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid
  exact cover (pullback.fst (projection R U V hVU) (projection R U V hVU))

local notation "selfCover" => representedCMNormalSelfPullbackFiniteEtale D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[simp] theorem representedCMNormalSelfPullbackFiniteEtale_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (selfCover R U V hVU existence geometry hRigid).obj.left =
      kernelPair R U V hVU := rfl

@[simp] theorem representedCMNormalSelfPullbackFiniteEtale_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (selfCover R U V hVU existence geometry hRigid).obj.hom =
      pullback.fst (projection R U V hVU) (projection R U V hVU) := rfl

/-- In the original represented normal tower, the remaining etaleness
condition is exactly flatness of the identical original projection. -/
theorem representedCMNormalProjection_etale_iff_flat_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    Etale (projection R U V hVU) ↔ Flat (projection R U V hVU) := by
  have : FormallyUnramified (projection R U V hVU) :=
    representedCMNormalProjection_formallyUnramified_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid
  have : IsLocallyNoetherian ((schemes R).obj U) := (R U).base.property.locallyNoetherian
  have : LocallyOfFinitePresentation (projection R U V hVU) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  constructor
  · intro hEtale
    exact inferInstance
  · intro hFlat
    exact AlgebraicGeometry.Etale.of_formallyUnramified_of_flat (projection R U V hVU)

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- Formal unramifiedness for the direct original chosen forgetting map. -/
theorem cmNormalProjection_formallyUnramified_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    FormallyUnramified ((chosenSchemes q).map (smallCMInclusion D hVU)) :=
  representedCMNormalProjection_formallyUnramified_of_dualGeometry D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid

/-- The finite-etale self-pullback for exactly the witnesses defining
cmSchemeTower and its original forgetting map. -/
def cmNormalSelfPullbackFiniteEtale
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    Cover ((chosenSchemes q).obj V) :=
  selfCover (chosenReps q) U V hVU existence geometry hRigid

local notation "chosenSelfCover" => cmNormalSelfPullbackFiniteEtale D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

@[simp] theorem cmNormalSelfPullbackFiniteEtale_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (chosenSelfCover existence geometry hRigid).obj.left =
      kernelPair (chosenReps q) U V hVU := rfl

@[simp] theorem cmNormalSelfPullbackFiniteEtale_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    (chosenSelfCover existence geometry hRigid).obj.hom =
      pullback.fst ((chosenSchemes q).map (smallCMInclusion D hVU))
        ((chosenSchemes q).map (smallCMInclusion D hVU)) := rfl

theorem cmNormalProjection_etale_iff_flat_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj) :
    Etale ((chosenSchemes q).map (smallCMInclusion D hVU)) ↔
      Flat ((chosenSchemes q).map (smallCMInclusion D hVU)) :=
  representedCMNormalProjection_etale_iff_flat_of_dualGeometry D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
