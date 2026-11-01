import Langlands.Shimura.PEL.HarrisTaylorCMNormalFiniteness
import Langlands.Shimura.PEL.HarrisTaylorCMSchemeSurjectivity

/-! # Quotient topology of original CM normal projections -/

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

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
/-- Original normal forgetting is a quotient map on actual scheme points. -/
theorem representedCMNormalProjection_isQuotientMap
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    Topology.IsQuotientMap (projection R U V hVU) :=
  (projection R U V hVU).isClosedMap.isQuotientMap
    (projection R U V hVU).continuous
    (representedCMSchemeTower_map_surjective D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R
      existence geometry (smallCMInclusion D hVU))

/-- Saturation under original forgetting is exactly the union of original
residual translates. -/
theorem representedCMNormalProjection_preimage_image
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (s : Set ((schemes R).obj V)) :
    projection R U V hVU ⁻¹' (projection R U V hVU '' s) =
      ⋃ g : SmallCMResidualGroup D U V,
        (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base '' s := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨g, hg⟩ := representedCMNormalPoint_exists_translate D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry z x hzx
    exact Set.mem_iUnion.mpr ⟨g, z, hz, hg⟩
  · intro hx
    obtain ⟨g, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨z, hz, ?_⟩
    change projection R U V hVU z =
      (((quotientAction R U V hVU).ρ g) ≫ projection R U V hVU) z
    rw [representedCMNormalProjection_invariant]
    rfl

/-- Every original normal forgetting morphism is open on actual scheme points. -/
theorem representedCMNormalProjection_isOpenMap
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    IsOpenMap (projection R U V hVU) := by
  intro s hs
  apply (representedCMNormalProjection_isQuotientMap D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU
    existence geometry).isCoinducing.isOpen_preimage.mp
  rw [representedCMNormalProjection_preimage_image D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU
    existence geometry]
  apply isOpen_iUnion
  intro g
  exact ((quotientAction R U V hVU).ρAut g).hom.homeomorph.isOpenMap s hs

/-- Invariant original fine-level open sets, using the actual residual maps. -/
abbrev representedCMNormalInvariantOpens :=
  {W : ((schemes R).obj V).Opens // ∀ g : SmallCMResidualGroup D U V,
    (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base ⁻¹'
      (W : Set ((schemes R).obj V)) = (W : Set ((schemes R).obj V))}

local notation "invariantOpens" => representedCMNormalInvariantOpens D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Pullback of a coarse open set is invariant under the original residual maps. -/
def representedCMNormalOpenPullback (W : ((schemes R).obj U).Opens) :
    invariantOpens R U V hVU :=
  ⟨⟨projection R U V hVU ⁻¹' (W : Set _),
    W.isOpen.preimage (projection R U V hVU).continuous⟩, by
    intro g
    ext x
    change projection R U V hVU
      ((Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base x) ∈ W ↔ _
    change ((((quotientAction R U V hVU).ρ g) ≫ projection R U V hVU) x) ∈ W ↔ _
    rw [representedCMNormalProjection_invariant]
    rfl⟩

local notation "openPullback" => representedCMNormalOpenPullback D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The image of an invariant fine open is a concrete open of the original
coarse scheme. -/
def representedCMNormalOpenDescend
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : invariantOpens R U V hVU) : ((schemes R).obj U).Opens :=
  ⟨projection R U V hVU '' (W.val : Set _),
    representedCMNormalProjection_isOpenMap D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry _ W.val.isOpen⟩

local notation "openDescend" => representedCMNormalOpenDescend D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Every invariant original fine open is exactly the preimage of its image. -/
theorem representedCMNormalOpenPullback_descend
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : invariantOpens R U V hVU) :
    openPullback R U V hVU (openDescend R U V hVU existence geometry W) = W := by
  apply Subtype.ext
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨g, hg⟩ := representedCMNormalPoint_exists_translate D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry z x hzx
    have hz' : z ∈
        (Scheme.Hom.toLRSHom ((quotientAction R U V hVU).ρ g)).base ⁻¹'
          (W.val : Set ((schemes R).obj V)) := by
      rw [W.property g]
      exact hz
    exact hg ▸ hz'
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Surjectivity of the same original projection gives the other inverse law. -/
theorem representedCMNormalOpenDescend_pullback
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : ((schemes R).obj U).Opens) :
    openDescend R U V hVU existence geometry (openPullback R U V hVU W) = W := by
  apply TopologicalSpace.Opens.ext
  exact Set.image_preimage_eq _
    (representedCMSchemeTower_map_surjective D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R
      existence geometry (smallCMInclusion D hVU))

/-- The opens of the exact coarse scheme are the invariant opens of the exact
fine scheme, with original pullback and image as inverse order maps. -/
def representedCMNormalOpensOrderIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    ((schemes R).obj U).Opens ≃o invariantOpens R U V hVU where
  toFun := openPullback R U V hVU
  invFun := openDescend R U V hVU existence geometry
  left_inv := representedCMNormalOpenDescend_pullback D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU
    existence geometry
  right_inv := representedCMNormalOpenPullback_descend D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU
    existence geometry
  map_rel_iff' := by
    intro W Z
    change (projection R U V hVU ⁻¹' (W : Set ((schemes R).obj U))) ⊆
      (projection R U V hVU ⁻¹' (Z : Set ((schemes R).obj U))) ↔
        (W : Set ((schemes R).obj U)) ⊆ (Z : Set ((schemes R).obj U))
    exact (representedCMSchemeTower_map_surjective D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R
      existence geometry (smallCMInclusion D hVU)).preimage_subset_preimage_iff

@[simp] theorem representedCMNormalOpensOrderIso_apply_coe
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : ((schemes R).obj U).Opens) :
    ((representedCMNormalOpensOrderIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor R U V hVU
        existence geometry W).val : Set ((schemes R).obj V)) =
      projection R U V hVU ⁻¹' (W : Set ((schemes R).obj U)) := rfl

@[simp] theorem representedCMNormalOpensOrderIso_symm_apply_coe
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : invariantOpens R U V hVU) :
    ((representedCMNormalOpensOrderIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor R U V hVU
        existence geometry).symm W : Set ((schemes R).obj U)) =
      projection R U V hVU '' (W.val : Set ((schemes R).obj V)) := rfl

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenAction" => cmNormalQuotientAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

omit [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
/-- The exact chosen forgetting map is a topological quotient map. -/
theorem cmNormalProjection_isQuotientMap
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    Topology.IsQuotientMap ((chosenSchemes q).map (smallCMInclusion D hVU)) :=
  representedCMNormalProjection_isQuotientMap D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry

/-- Saturation uses the identical chosen residual action and projection. -/
theorem cmNormalProjection_preimage_image
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (s : Set ((chosenSchemes q).obj V)) :
    (chosenSchemes q).map (smallCMInclusion D hVU) ⁻¹'
      ((chosenSchemes q).map (smallCMInclusion D hVU) '' s) =
        ⋃ g : SmallCMResidualGroup D U V,
          (Scheme.Hom.toLRSHom ((chosenAction q).ρ g)).base '' s :=
  representedCMNormalProjection_preimage_image D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry s

/-- The original forgetting map of the exact chosen tower is open. -/
theorem cmNormalProjection_isOpenMap
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    IsOpenMap ((chosenSchemes q).map (smallCMInclusion D hVU)) :=
  representedCMNormalProjection_isOpenMap D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry

/-- Invariant opens for precisely the witnesses defining `cmSchemeTower`. -/
abbrev cmNormalInvariantOpens :=
  invariantOpens (chosenReps q) U V hVU

local notation "chosenInvariantOpens" => cmNormalInvariantOpens D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

/-- Original chosen pullback, taking values in the original invariant opens. -/
def cmNormalOpenPullback (W : ((chosenSchemes q).obj U).Opens) :
    chosenInvariantOpens :=
  openPullback (chosenReps q) U V hVU W

local notation "chosenOpenPullback" => cmNormalOpenPullback D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

/-- Original chosen image of an invariant open. -/
def cmNormalOpenDescend
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : chosenInvariantOpens) : ((chosenSchemes q).obj U).Opens :=
  openDescend (chosenReps q) U V hVU existence geometry W

local notation "chosenOpenDescend" => cmNormalOpenDescend D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

theorem cmNormalOpenPullback_descend
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : chosenInvariantOpens) :
    chosenOpenPullback (chosenOpenDescend existence geometry W) = W :=
  representedCMNormalOpenPullback_descend D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry W

theorem cmNormalOpenDescend_pullback
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : ((chosenSchemes q).obj U).Opens) :
    chosenOpenDescend existence geometry (chosenOpenPullback W) = W :=
  representedCMNormalOpenDescend_pullback D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry W

/-- Opens of the original chosen coarse scheme are exactly invariant opens of
its original chosen fine scheme. -/
def cmNormalOpensOrderIso
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    ((chosenSchemes q).obj U).Opens ≃o chosenInvariantOpens :=
  representedCMNormalOpensOrderIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry

local notation "chosenOpensOrderIso" => cmNormalOpensOrderIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

@[simp] theorem cmNormalOpensOrderIso_apply_coe
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : ((chosenSchemes q).obj U).Opens) :
    (chosenOpensOrderIso existence geometry W).val.carrier =
      (chosenSchemes q).map (smallCMInclusion D hVU) ⁻¹'
        (W : Set ((chosenSchemes q).obj U)) := rfl

@[simp] theorem cmNormalOpensOrderIso_symm_apply_coe
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (W : chosenInvariantOpens) :
    ((chosenOpensOrderIso existence geometry).symm W :
        Set ((chosenSchemes q).obj U)) =
      (chosenSchemes q).map (smallCMInclusion D hVU) ''
        W.val.carrier := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
