import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Lattice

/-! # The centralizer of a split torus from the centralizers of its cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- On a split torus the identity is a finite sum of characters followed by cocharacters. -/
theorem IsSplitTorus.exists_sum_comp_eq_id (hT : IsSplitTorus T.toGrp) :
    ∃ (I : Type u) (_ : Fintype I) (π : I → characterLattice T) (s : I → cocharacterLattice T),
      ∑ j, π j ≫ s j = 𝟙 T := by
  obtain ⟨I, _, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let eh : T ⟶ splitTorus.commGroupScheme S I := Additive.ofMul e.hom
  let ei : splitTorus.commGroupScheme S I ⟶ T := Additive.ofMul e.inv
  refine ⟨I, inferInstance, fun j => eh ≫ splitTorus.proj S I j,
    fun j => splitTorus.single S I j ≫ ei, ?_⟩
  calc ∑ j, (eh ≫ splitTorus.proj S I j) ≫ splitTorus.single S I j ≫ ei
      = eh ≫ (∑ j, splitTorus.proj S I j ≫ splitTorus.single S I j) ≫ ei := by
        simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    _ = 𝟙 T := by
        rw [splitTorus.sum_proj_comp_single, Category.id_comp]
        exact congrArg Additive.ofMul e.hom_inv_id

/-- A subgroup functor that centralizes every cocharacter of a split torus centralizes the
whole torus. -/
theorem le_torusCentralizer_of_le_dynamicCentralizer (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) {F : SubgroupFunctor G}
    (hF : ∀ c : cocharacterLattice T,
      F ≤ Dynamic.centralizer (CommGroupScheme.groupHom c ≫ i)) :
    F ≤ torusCentralizer i := by
  obtain ⟨I, _, π, s, hsum⟩ := hT.exists_sum_comp_eq_id
  intro U g hg V a t
  have ht : t = ∏ j, t ≫ (CommGroupScheme.groupHom (π j ≫ s j)).hom.hom := by
    rw [← comp_groupHom_sum, hsum]
    exact (Category.comp_id t).symm
  rw [ht]
  refine Finset.prod_induction _ (fun x : V ⟶ T.X => Commute (a ≫ g) (x ≫ i.hom.hom))
    (fun x y hx hy => ?_) ?_ (fun j _ => ?_)
  · rw [MonObj.mul_comp]
    exact hx.mul_right hy
  · rw [MonObj.one_comp]
    exact Commute.one_right _
  · have hc := hF (s j) U hg
    rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hc
    have h := hc V a (t ≫ (CommGroupScheme.groupHom (π j)).hom.hom)
    rwa [Grp.comp_hom_hom, ← Category.assoc, ← comp_groupHom_comp] at h

end Langlands.GroupScheme
