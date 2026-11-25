/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Lifting sections along epimorphisms of sheaves on the affine pro-étale site

Let `g : G ⟶ H` be an epimorphism of abelian sheaves on the affine pro-étale site `S.AffineProEt`
and `s` a section of `H` over `V`. Then `s` lifts to `G` after pulling back along a single
surjection `W ⟶ V`: the image sieve of `s` contains a finite jointly surjective family, which
factors through its disjoint union `W`, and the local lifts glue over the pairwise disjoint
pieces of `W`.

## Main statements

* `AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_factorization_disjoint`: a finite
  jointly surjective family factors through a single surjection, with pairwise disjoint pieces.
* `AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_lift_of_epi`: sections of an
  epimorphism of abelian sheaves lift after pullback along a single surjection.
* `AlgebraicGeometry.Scheme.AffineProEt.ofArrows_mem_topology_of_surjective`: a single surjection
  generates a covering sieve.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

/-- Distinct components of the disjoint union `Spec (∏ᵢ Γ(V i))` have disjoint images. -/
lemma disjoint_range_sigmaCoverι {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X) {i k : ι} (hik : i ≠ k) :
    Disjoint (Set.range (sigmaCoverι V f i).left.base)
      (Set.range (sigmaCoverι V f k).left.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨p, -, -⟩ := exists_left_base_preimage
    (IsPullback.of_hasPullback (sigmaCoverι V f i) (sigmaCoverι V f k)) a b hb.symm
  exact (isEmpty_of_sigmaCoverι_eq V f hik _ _ pullback.condition).elim p

/-- Given a finite jointly surjective family `f i : V i ⟶ X` in the affine pro-étale site, the
family factors through a single surjection `q : W ⟶ X` such that the pieces `j i : V i ⟶ W` form
a Zariski cover of `W` by pairwise disjoint open subschemes. -/
lemma exists_surjective_factorization_disjoint {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ X) (j : ∀ i, V i ⟶ W),
      Surjective q.left ∧ (∀ i, j i ≫ q = f i) ∧ (∀ i, IsOpenImmersion (j i).left) ∧
      (∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base)) ∧
      ∀ i k, i ≠ k → Disjoint (Set.range (j i).left.base) (Set.range (j k).left.base) :=
  ⟨sigmaCover V f, sigmaCoverπ V f, sigmaCoverι V f, surjective_sigmaCoverπ V f hsurj,
    sigmaCoverι_π V f, isOpenImmersion_sigmaCoverι V f, exists_mem_range_sigmaCoverι V f,
    fun _ _ ↦ disjoint_range_sigmaCoverι V f⟩

/-- A single surjection `q : W ⟶ V` in the affine pro-étale site, viewed as a family indexed by
`Fin 1`, generates a covering sieve. -/
lemma ofArrows_mem_topology_of_surjective {W V : S.AffineProEt} (q : W ⟶ V)
    (hq : Surjective q.left) :
    Sieve.ofArrows (fun _ : Fin 1 ↦ W) (fun _ ↦ q) ∈ topology S V := by
  refine (topology S).superset_covering ?_ (generate_singleton_mem_topology q hq)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  exact Sieve.ofArrows_mk _ _ 0

/-- **Sections of an epimorphism of sheaves lift along a surjection.** Let `g : G ⟶ H` be an
epimorphism of abelian sheaves on the affine pro-étale site and `s` a section of `H` over `V`.
Then there is a surjection `q : W ⟶ V` such that the restriction of `s` to `W` lifts to `G`. -/
theorem exists_surjective_lift_of_epi (V : S.AffineProEt)
    {G H : Sheaf (topology S) AddCommGrpCat.{u + 1}} (g : G ⟶ H) [Epi g]
    (s : H.obj.obj (op V)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ V) (t : G.obj.obj (op W)),
      Surjective q.left ∧ g.hom.app (op W) t = H.obj.map q.op s := by
  have : Presheaf.IsLocallySurjective (topology S) g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} g).2 inferInstance
  obtain ⟨ι, _, Vi, f, hf, hsurj⟩ :=
    exists_finite_jointly_surjective_of_mem_topology (Presheaf.imageSieve_mem _ g.hom s)
  choose t ht using hf
  have hG := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ G.obj (CategoryTheory.forget AddCommGrpCat) G.property)
  have hH := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ H.obj (CategoryTheory.forget AddCommGrpCat) H.property)
  obtain ⟨z, hz⟩ := exists_sigmaCover_glue Vi f ((isSheaf_iff_isSheaf_of_type _ _).mpr hG) t
  refine ⟨sigmaCover Vi f, sigmaCoverπ Vi f, z, surjective_sigmaCoverπ Vi f hsurj, ?_⟩
  refine sigmaCover_ext (F := H.obj ⋙ CategoryTheory.forget _) Vi f
    ((isSheaf_iff_isSheaf_of_type _ _).mpr hH) fun i ↦ ?_
  have hz' : G.obj.map (sigmaCoverι Vi f i).op z = t i := hz i
  have key : H.obj.map (sigmaCoverι Vi f i).op (g.hom.app _ z) =
      H.obj.map (sigmaCoverι Vi f i).op (H.obj.map (sigmaCoverπ Vi f).op s) := by
    rw [← NatTrans.naturality_apply, hz', ht i, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, sigmaCoverι_π]
  exact key

/-- `exists_surjective_lift_of_epi` in the shape of a family indexed by `Fin 1` of objects over
`V`, as needed for the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_lift`. -/
theorem exists_surjective_over_lift_of_epi (V : S.AffineProEt)
    {G H : Sheaf (topology S) AddCommGrpCat.{u + 1}} (g : G ⟶ H) [Epi g]
    (s : H.obj.obj (op V)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ V), Surjective q.left ∧
      ∀ a : Fin 1, ∃ t : G.obj.obj (op ((fun _ : Fin 1 ↦ Over.mk q) a).left),
        g.hom.app _ t = H.obj.map ((fun _ : Fin 1 ↦ Over.mk q) a).hom.op s := by
  obtain ⟨W, q, t, hq, ht⟩ := exists_surjective_lift_of_epi V g s
  exact ⟨W, q, hq, fun _ ↦ ⟨t, ht⟩⟩

end AlgebraicGeometry.Scheme.AffineProEt
