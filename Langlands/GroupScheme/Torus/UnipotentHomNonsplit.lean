import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.Unipotent.TorusHom

/-! # Homomorphisms from affine unipotent groups to arbitrary tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism from an affine unipotent group to an arbitrary torus is zero. -/
theorem IsUnipotent.hom_eq_zero_of_isTorus [IsAffineHom H.X.hom]
    (hH : IsUnipotent H) (hG : IsTorus G) (f : H ⟶ G) : f = 0 := by
  obtain ⟨K, _, _, hGK⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have h := (hH.baseChange (K := K)).hom_eq_zero_of_isSplitTorus hGK
    ((GroupScheme.baseChange b).map f)
  have := GaloisCocharacterDescent.faithful_algebraPullback k K
  apply (Grp.forget _).map_injective
  change f.hom.hom = (1 : H.X ⟶ G.X)
  apply (Over.pullback b).map_injective
  rw [Functor.map_one]
  exact congrArg (fun g => g.hom.hom) h

/-- Such a homomorphism is the identity on every scheme test. -/
theorem IsUnipotent.comp_eq_one_of_isTorus [IsAffineHom H.X.hom]
    (hH : IsUnipotent H) (hG : IsTorus G) (f : H ⟶ G)
    (S : Over (Spec (CommRingCat.of k))) (x : S ⟶ H.X) :
    x ≫ f.hom.hom = 1 := by
  rw [hH.hom_eq_zero_of_isTorus hG f]
  exact MonObj.comp_one x

/-- The image on every scheme test is the identity subgroup. -/
theorem IsUnipotent.range_eq_bot_to_isTorus [IsAffineHom H.X.hom]
    (hH : IsUnipotent H) (hG : IsTorus G) (f : H ⟶ G) :
    SubgroupFunctor.range f = ⊥ := by
  rw [hH.hom_eq_zero_of_isTorus hG f, SubgroupFunctor.range_zero]

/-- There is exactly one homomorphism from an affine unipotent group to a torus. -/
@[instance_reducible] def IsUnipotent.uniqueHomToTorus [IsAffineHom H.X.hom]
    (hH : IsUnipotent H) (hG : IsTorus G) : Unique (H ⟶ G) where
  default := 0
  uniq f := hH.hom_eq_zero_of_isTorus hG f

/-- A homomorphism through an arbitrary torus from an affine unipotent group is zero. -/
theorem IsUnipotent.comp_eq_zero_of_isTorus [IsAffineHom H.X.hom]
    (hH : IsUnipotent H)
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T)
    (f : H ⟶ T) (i : T ⟶ G) : f ≫ i = 0 := by
  rw [hH.hom_eq_zero_of_isTorus hT f, zero_comp]

/-- A represented affine unipotent subgroup contained in a monic torus is trivial. -/
theorem IsUnipotent.range_eq_bot_of_range_le_isTorus [IsAffineHom H.X.hom]
    (hH : IsUnipotent H)
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T)
    (f : H ⟶ G) (i : T ⟶ G) [Mono f.hom.hom] [Mono i.hom.hom]
    (h : SubgroupFunctor.range f ≤ SubgroupFunctor.range i) :
    SubgroupFunctor.range f = ⊥ := by
  let g := SubgroupFunctor.factorOfRangeLE h
  have hg : g ≫ i = f := SubgroupFunctor.factorOfRangeLE_comp h
  have hf : f = 0 := hg.symm.trans (hH.comp_eq_zero_of_isTorus hT g i)
  rw [hf, SubgroupFunctor.range_zero]

end Langlands.GroupScheme
