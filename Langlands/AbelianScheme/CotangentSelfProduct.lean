import Langlands.AbelianScheme.LieAdditivityProof
import Langlands.AlgebraicGeometry.Picard.DualMapEqualityLocus

/-! # Cotangent sections of an actual abelian self-product -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open Langlands.Scheme
open scoped CategoryTheory.MonObj

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 85000

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}}

private def topSectionsMap {M N : S.Modules} (f : M ⟶ N) :
    Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ(N, ⊤) where
  toFun := f.app ⊤
  map_add' := (f.app ⊤).hom.map_add
  map_smul' r z := f.app_smul r z

private lemma topSectionsMap_comp {M N P : S.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    topSectionsMap (f ≫ g) = (topSectionsMap g).comp (topSectionsMap f) := rfl

private lemma topSectionsMap_add {M N : S.Modules} (f g : M ⟶ N) :
    topSectionsMap (f + g) = topSectionsMap f + topSectionsMap g := rfl

private lemma topSectionsMap_id (M : S.Modules) : topSectionsMap (𝟙 M) = LinearMap.id := rfl

private lemma topSectionsMap_zero (M N : S.Modules) :
    topSectionsMap (0 : M ⟶ N) = 0 := rfl

private lemma sectionsProd_coprod {M N : S.Modules} (x y : M ⟶ N) (a b : N ⟶ M)
    (hxa : x ≫ a = 𝟙 M) (hxb : x ≫ b = 0) (hya : y ≫ a = 0) (hyb : y ≫ b = 𝟙 M) :
    ((topSectionsMap a).prod (topSectionsMap b)).comp
      ((topSectionsMap x).coprod (topSectionsMap y)) = LinearMap.id := by
  let X := topSectionsMap x
  let Y := topSectionsMap y
  let A := topSectionsMap a
  let B' := topSectionsMap b
  have h1 : A.comp X = LinearMap.id :=
    (topSectionsMap_comp x a).symm.trans ((congrArg topSectionsMap hxa).trans (topSectionsMap_id _))
  have h2 : B'.comp X = 0 :=
    (topSectionsMap_comp x b).symm.trans ((congrArg topSectionsMap hxb).trans (topSectionsMap_zero _ _))
  have h3 : A.comp Y = 0 :=
    (topSectionsMap_comp y a).symm.trans ((congrArg topSectionsMap hya).trans (topSectionsMap_zero _ _))
  have h4 : B'.comp Y = LinearMap.id :=
    (topSectionsMap_comp y b).symm.trans ((congrArg topSectionsMap hyb).trans (topSectionsMap_id _))
  apply LinearMap.ext
  rintro ⟨u, v⟩
  apply Prod.ext
  · change A (X u + Y v) = u
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, h1, h3,
      LinearMap.id_apply, LinearMap.zero_apply, add_zero]
  · change B' (X u + Y v) = v
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, h2, h4,
      LinearMap.zero_apply, LinearMap.id_apply, zero_add]

private abbrev firstProjector (G : GroupScheme S) := GroupScheme.cotangentMap (fst G G)
private abbrev secondProjector (G : GroupScheme S) := GroupScheme.cotangentMap (snd G G)
private abbrev firstAxis (G : GroupScheme S) [IsCommMonObj G.X] :=
  GroupScheme.cotangentMap (lift (𝟙 G) (1 : G ⟶ G))
private abbrev secondAxis (G : GroupScheme S) [IsCommMonObj G.X] :=
  GroupScheme.cotangentMap (lift (1 : G ⟶ G) (𝟙 G))

private lemma firstProjector_firstAxis (G : GroupScheme S) [IsCommMonObj G.X] :
    firstProjector G ≫ firstAxis G = 𝟙 _ := by
  dsimp only [firstProjector, firstAxis]
  rw [← GroupScheme.cotangentMap_comp, lift_fst, GroupScheme.cotangentMap_id]

private lemma firstProjector_secondAxis (G : GroupScheme S) [IsCommMonObj G.X] :
    firstProjector G ≫ secondAxis G = 0 := by
  dsimp only [firstProjector, secondAxis]
  rw [← GroupScheme.cotangentMap_comp, lift_fst, GroupScheme.cotangentMap_one]

private lemma secondProjector_firstAxis (G : GroupScheme S) [IsCommMonObj G.X] :
    secondProjector G ≫ firstAxis G = 0 := by
  dsimp only [secondProjector, firstAxis]
  rw [← GroupScheme.cotangentMap_comp, lift_snd, GroupScheme.cotangentMap_one]

private lemma secondProjector_secondAxis (G : GroupScheme S) [IsCommMonObj G.X] :
    secondProjector G ≫ secondAxis G = 𝟙 _ := by
  dsimp only [secondProjector, secondAxis]
  rw [← GroupScheme.cotangentMap_comp, lift_snd, GroupScheme.cotangentMap_id]

private lemma axisProjector_sum (G : GroupScheme S) [IsCommMonObj G.X] :
    (firstAxis G ≫ firstProjector G) + (secondAxis G ≫ secondProjector G) =
      𝟙 (GroupScheme.cotangentAtIdentity (G ⊗ G)) := by
  apply sub_eq_zero.mp
  apply GroupScheme.cotangentMap_fst_snd_ext (H := G)
  · change firstProjector G ≫ _ = _
    rw [Preadditive.comp_sub, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
      firstProjector_firstAxis, firstProjector_secondAxis, Category.id_comp,
      zero_comp, add_zero, Category.comp_id, sub_self]
  · change secondProjector G ≫ _ = _
    rw [Preadditive.comp_sub, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
      secondProjector_firstAxis, secondProjector_secondAxis, Category.id_comp,
      zero_comp, zero_add, Category.comp_id, sub_self]

private lemma axisSections_projectorSections (G : GroupScheme S) [IsCommMonObj G.X] :
    ((topSectionsMap (firstAxis G)).prod (topSectionsMap (secondAxis G))).comp
      ((topSectionsMap (firstProjector G)).coprod (topSectionsMap (secondProjector G))) =
        LinearMap.id :=
  sectionsProd_coprod _ _ _ _ (firstProjector_firstAxis G) (firstProjector_secondAxis G)
    (secondProjector_firstAxis G) (secondProjector_secondAxis G)

private lemma projectorSections_axisSections (G : GroupScheme S) [IsCommMonObj G.X] :
    ((topSectionsMap (firstProjector G)).coprod (topSectionsMap (secondProjector G))).comp
      ((topSectionsMap (firstAxis G)).prod (topSectionsMap (secondAxis G))) =
        LinearMap.id := by
  have hs : (topSectionsMap (firstProjector G)).comp (topSectionsMap (firstAxis G)) +
      (topSectionsMap (secondProjector G)).comp (topSectionsMap (secondAxis G)) =
        LinearMap.id := by
    rw [← topSectionsMap_comp, ← topSectionsMap_comp, ← topSectionsMap_add,
      axisProjector_sum, topSectionsMap_id]
  apply LinearMap.ext
  exact LinearMap.congr_fun hs

private def cotangentTensorEquiv (G : GroupScheme S) [IsCommMonObj G.X] :
    Γ(GroupScheme.cotangentAtIdentity (G ⊗ G), ⊤) ≃ₗ[Γ(S, ⊤)]
      (Γ(GroupScheme.cotangentAtIdentity G, ⊤) × Γ(GroupScheme.cotangentAtIdentity G, ⊤)) :=
  LinearEquiv.ofLinearMap
    ((topSectionsMap (firstAxis G)).prod (topSectionsMap (secondAxis G)))
    ((topSectionsMap (firstProjector G)).coprod (topSectionsMap (secondProjector G)))
    (axisSections_projectorSections G) (projectorSections_axisSections G)

/-- The two coordinate sections of the actual abelian self-product identify
its identity cotangent sections with the product of the two cotangent modules. -/
def cotangentSelfProductEquiv (B : AbelianScheme S) :
    Γ(GroupScheme.cotangentAtIdentity (DualMapEquality.square B).toGrp, ⊤) ≃ₗ[Γ(S, ⊤)]
      (Γ(GroupScheme.cotangentAtIdentity B.toGrp, ⊤) × Γ(GroupScheme.cotangentAtIdentity B.toGrp, ⊤)) :=
  cotangentTensorEquiv B.toGrp

end Langlands.AbelianScheme
