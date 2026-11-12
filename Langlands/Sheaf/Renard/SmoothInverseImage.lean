import Langlands.Sheaf.Renard.ActionInverseImage
import Langlands.Sheaf.Renard.LocalSmoothComparison
import Langlands.Sheaf.Renard.SmoothStalkRestriction
import Langlands.Sheaf.Equivariant.SmoothDirectImageCoreflector

/-!
# Smoothness of the actual action-sheaf inverse image

The adjunction unit factors through the smooth subsheaf after direct image.
Transposing this factorization gives a splitting of the smooth inclusion in
the actual inverse image, so the entire inverse-image sheaf is smooth.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.SectionActions

open CategoryTheory
open Langlands.Sheaf.Equivariant

variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [MulAction G Y]
variable [ContinuousSMul G X] [ContinuousSMul G Y]
variable (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

section Local

variable [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]

/-- Transpose of the locally smooth factorization of the actual adjunction unit. -/
def inverseImageToSmooth (F : ActionSheaf G Y) (hF : IsSmoothSheaf ℂ G Y F) :
    (actionInverseImage f hf).obj F ⟶
      (smoothSubsheafFunctor ℂ).obj ((actionInverseImage f hf).obj F) :=
  ((actionInverseImageAdjunction f hf).homEquiv F _).symm
    (Langlands.Sheaf.Equivariant.smoothLift ℂ hF
        ((actionInverseImageAdjunction f hf).unit.app F) ≫
      SmoothDirectImage.preimageSmoothMap f hf ((actionInverseImage f hf).obj F))

/-- The factorization is a right inverse to the original smooth inclusion. -/
@[reassoc]
theorem inverseImageToSmooth_inclusion (F : ActionSheaf G Y)
    (hF : IsSmoothSheaf ℂ G Y F) :
    inverseImageToSmooth f hf F hF ≫
        (smoothSubsheafι ℂ).app ((actionInverseImage f hf).obj F) = 𝟙 _ := by
  apply ((actionInverseImageAdjunction f hf).homEquiv F _).injective
  rw [Adjunction.homEquiv_naturality_right, inverseImageToSmooth,
    Equiv.apply_symm_apply, Category.assoc,
    SmoothDirectImage.preimageSmoothMap_inclusion]
  change (actionInverseImageAdjunction f hf).unit.app F = _
  exact ((actionInverseImageAdjunction f hf).homEquiv_id F).symm

/-- The entire actual inverse-image sheaf is locally smooth. -/
theorem isSmoothSheaf_actionInverseImage (F : ActionSheaf G Y)
    (hF : IsSmoothSheaf ℂ G Y F) :
    IsSmoothSheaf ℂ G X ((actionInverseImage f hf).obj F) := by
  let k := inverseImageToSmooth f hf F hF
  let : Mono k := (show SplitMono k from
    { retraction := (smoothSubsheafι ℂ).app ((actionInverseImage f hf).obj F)
      id := inverseImageToSmooth_inclusion f hf F hF }).mono
  exact IsSmoothSheaf.of_mono ℂ k (isSmoothSheaf_smoothSubsheaf ℂ _)

end Local

/-- Renard smoothness is preserved by the actual inverse image. -/
theorem isSmoothAction_actionInverseImage
    (hG : Langlands.Topology.IsLocallyProfinite G)
    (hY : Langlands.Topology.IsLocallyProfinite Y)
    (F : ActionSheaf G Y) (hF : IsSmoothAction F) :
    IsSmoothAction ((actionInverseImage f hf).obj F) := by
  let := hasStableNeighbourhoods_of_locallyProfinite (G := G) (X := X) hG
  let := hasStableNeighbourhoods_of_locallyProfinite (G := G) (X := Y) hG
  exact CompactSections.isSmooth_representation_of_isSmoothSheaf
    (isSmoothSheaf_actionInverseImage f hf F (isSmoothSheaf_of_isSmoothAction F hY hF))

/-- Lift the actual Kan-extension/sheafification inverse image to smooth actions. -/
def smoothActionInverseImage
    (hG : Langlands.Topology.IsLocallyProfinite G)
    (hY : Langlands.Topology.IsLocallyProfinite Y) :
    SmoothActionSheaf G Y ⥤ SmoothActionSheaf G X :=
  (smoothActionProperty G X).lift
    (smoothActionInclusion G Y ⋙ actionInverseImage f hf)
    (fun F => isSmoothAction_actionInverseImage f hf hG hY F.obj F.property)

/-- Forgetting the smoothness proof recovers the original inverse image. -/
def smoothActionInverseImageToActionIso
    (hG : Langlands.Topology.IsLocallyProfinite G)
    (hY : Langlands.Topology.IsLocallyProfinite Y) :
    smoothActionInverseImage f hf hG hY ⋙ smoothActionInclusion G X ≅
      smoothActionInclusion G Y ⋙ actionInverseImage f hf :=
  (smoothActionProperty G X).liftCompιIso _ _

section Subgroup

variable (Q : Subgroup G) {Z : Type} [TopologicalSpace Z]
variable [MulAction Q Z] [ContinuousSMul Q Z]
variable (i : C(Z, Y)) (hi : ∀ (q : Q) (z : Z), i (q • z) = (q : G) • i z)

/-- Smoothness of the whole original subgroup-space inverse image. -/
theorem isSmoothAction_subgroupSpaceRestriction
    (hG : Langlands.Topology.IsLocallyProfinite G) (hQ : IsClosed (Q : Set G))
    (hY : Langlands.Topology.IsLocallyProfinite Y)
    (F : ActionSheaf G Y) (hF : IsSmoothAction F) :
    IsSmoothAction ((subgroupSpaceRestriction Q i hi).obj F) := by
  have hQl : Langlands.Topology.IsLocallyProfinite Q :=
    Langlands.Topology.LocallyProfiniteProof.locallyClosedSubspaces
      G hG (Q : Set G) hQ.isLocallyClosed
  exact isSmoothAction_actionInverseImage i hi hQl hY
    ((subgroupRestriction Q).obj F) (isSmoothAction_subgroupRestriction Q F hF)

/-- Renard's restriction along a closed subgroup and an equivariant space map.
For a locally closed inclusion, this is the smooth restriction functor. -/
def smoothSubgroupSpaceRestriction
    (hG : Langlands.Topology.IsLocallyProfinite G) (hQ : IsClosed (Q : Set G))
    (hY : Langlands.Topology.IsLocallyProfinite Y) :
    SmoothActionSheaf G Y ⥤ SmoothActionSheaf Q Z :=
  (smoothActionProperty Q Z).lift
    (smoothActionInclusion G Y ⋙ subgroupSpaceRestriction Q i hi)
    (fun F => isSmoothAction_subgroupSpaceRestriction Q i hi hG hQ hY F.obj F.property)

/-- The smooth subgroup-space restriction retains the entire original sheaf and maps. -/
def smoothSubgroupSpaceRestrictionToActionIso
    (hG : Langlands.Topology.IsLocallyProfinite G) (hQ : IsClosed (Q : Set G))
    (hY : Langlands.Topology.IsLocallyProfinite Y) :
    smoothSubgroupSpaceRestriction Q i hi hG hQ hY ⋙ smoothActionInclusion Q Z ≅
      smoothActionInclusion G Y ⋙ subgroupSpaceRestriction Q i hi :=
  (smoothActionProperty Q Z).liftCompιIso _ _

end Subgroup

end Langlands.Sheaf.Renard.SectionActions
