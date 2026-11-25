/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Sheaves on the small étale site and disjoint covers

A sheaf `G` on the small étale site of a scheme `X` sends an object `V` covered by finitely
many pairwise disjoint subobjects `W i ⟶ V` to the product of the `G (W i)`
(`AlgebraicGeometry.Scheme.Etale.isIso_piLift_of_disjoint`): the sheaf condition for the cover
reads `G V ≅ ∏ G (W i)` because any two morphisms `Z ⟶ W i`, `Z ⟶ W j` agreeing on `V` are
either equal (`i = j`, the `W i ⟶ V` being monomorphisms) or have empty source (`i ≠ j`),
where `G` has terminal sections.

-/

@[expose] public section

universe u u' v'

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {A : Type u'} [Category.{v'} A] (G : Sheaf X.smallEtaleTopology A)
  {V : X.Etale} {ι : Type*} (W : ι → X.Etale) (π : ∀ i, W i ⟶ V)

/-- For pairwise disjoint subobjects `π i : W i ⟶ V` of the small étale site, every family of
morphisms `E ⟶ G (W i)` is compatible: two morphisms `Z ⟶ W i` and `Z ⟶ W j` agreeing on `V`
are equal if `i = j`, and have empty source otherwise. -/
lemma Etale.comp_map_eq_of_disjoint [∀ i, Mono (π i)]
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base))
    {E : A} (x : ∀ i, E ⟶ G.obj.obj (op (W i))) ⦃Z : X.Etale⦄ ⦃i j : ι⦄ (a : Z ⟶ W i)
    (b : Z ⟶ W j) (h : a ≫ π i = b ≫ π j) :
    x i ≫ G.obj.map a.op = x j ≫ G.obj.map b.op := by
  by_cases hij : i = j
  · subst hij
    obtain rfl : a = b := (cancel_mono (π i)).mp h
    rfl
  · -- the source `Z` is empty, so `G Z` is terminal
    have hZ : IsEmpty Z.left := ⟨fun z ↦ by
      have hz := congrArg (fun m ↦ m.left.base z) h
      change (a.left ≫ (π i).left) z = (b.left ≫ (π j).left) z at hz
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hz
      exact Set.disjoint_left.mp (hdisj i j hij) ⟨a.left z, rfl⟩ ⟨b.left z, hz.symm⟩⟩
    exact (Etale.isTerminalSectionsOfIsEmpty G Z).hom_ext _ _

/-- **A sheaf sends a disjoint cover to a product**: if the pairwise disjoint subobjects
`π i : W i ⟶ V` cover `V` in the small étale topology, then the restriction maps exhibit
`G V` as the product of the `G (W i)`.
(blueprint: `lem-weil-pbc-disjoint-etale-sections-product`) -/
theorem Etale.isIso_piLift_of_disjoint [∀ i, Mono (π i)]
    (hcov : Sieve.ofArrows W π ∈ X.smallEtaleTopology V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base))
    [HasProduct fun i ↦ G.obj.obj (op (W i))] :
    IsIso (Pi.lift fun i ↦ G.obj.map (π i).op) := by
  refine isIso_of_yoneda_map_bijective _ fun E ↦ ⟨fun x y hxy ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := G.property.existsUnique_amalgamation_ofArrows π hcov
      (fun i ↦ x ≫ G.obj.map (π i).op) (Etale.comp_map_eq_of_disjoint G W π hdisj _)
    refine (ht x fun i ↦ rfl).trans (ht y fun i ↦ ?_).symm
    simpa using (congrArg (· ≫ Pi.π _ i) hxy).symm
  · obtain ⟨t, ht, -⟩ := G.property.existsUnique_amalgamation_ofArrows π hcov
      (fun i ↦ φ ≫ Pi.π _ i) (Etale.comp_map_eq_of_disjoint G W π hdisj _)
    exact ⟨t, Pi.hom_ext _ _ fun i ↦ by simpa using ht i⟩

end AlgebraicGeometry.Scheme
