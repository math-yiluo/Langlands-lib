/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteFreeLocalLift
import WeilConjectures.AlgebraicGeometry.ModuleFiniteFreeLocalSupport

/-! # Finite support of a generating family near a point

Source: Stacks Project, Modules, Lemmas 01BB and 01B8.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem epi_overMap_of_factorization
    {X : TopCat.{u}} (R : X.Sheaf RingCat.{u})
    {V U W : TopologicalSpace.Opens X} (hUV : U ≤ V) (hWU : W ≤ U)
    {M N P : SheafOfModules.{u} (R.over V)}
    {L : SheafOfModules.{u} (R.over U)} (m : M ⟶ N) (p : N ⟶ P)
    (l : L ⟶ (overMap R (homOfLE hUV)).obj N)
    (a : (overMap R (homOfLE hWU)).obj L ⟶
      (overMap R (homOfLE (hWU.trans hUV))).obj M)
    (ha : a ≫ (overMap R (homOfLE (hWU.trans hUV))).map m =
      (overMap R (homOfLE hWU)).map l)
    [Epi (l ≫ (overMap R (homOfLE hUV)).map p)] :
    Epi ((overMap R (homOfLE (hWU.trans hUV))).map (m ≫ p)) := by
  let F := overMap R (homOfLE hWU)
  have hE : Epi (F.map (l ≫ (overMap R (homOfLE hUV)).map p)) := F.map_epi _
  have hfac : a ≫ (overMap R (homOfLE (hWU.trans hUV))).map (m ≫ p) =
      F.map (l ≫ (overMap R (homOfLE hUV)).map p) := by
    rw [Functor.map_comp, ← Category.assoc, ha, Functor.map_comp]
    rfl
  exact @epi_of_epi_fac _ _ _ _ _ a _ _ hE hfac

set_option backward.isDefEq.respectTransparency false in
/-- Near any point of an open on which a module sheaf is finite type, finitely many
members of a specified global generating family generate. Compactness is not assumed.

Source: Stacks Project, Modules, Lemma 01BB, first paragraph of the proof, applied
to the directed finite sub-coproducts of the free sheaf; Lemma 01B8.
https://stacks.math.columbia.edu/tag/01BB
https://stacks.math.columbia.edu/tag/01B8
(blueprint: lem-weil-pbc-module-generating-sections-local-selection).

Proof: Restrict to K and choose a finite local generating family near x, using
finite type. The given epimorphism from the free sheaf on sigma.I locally lifts
these finitely many generators, after intersecting finitely many neighbourhoods.
Each lifted germ is a finite sum of basis germs: the free sheaf is the filtered
colimit of its finite sub-coproducts, and stalks preserve this colimit. Take the
union S of the supports of these finitely many germs. Represent their lifts in
the finite free sheaf on S and shrink the neighbourhood so that the images of
the lifts equal the chosen generating sections as sections. The finite-support
map is then epi on this neighbourhood because its image contains the local
generators. Restriction preserves free sheaves and their basis maps, so this is
the stated overMap morphism. If the local generating family is empty, choose
S empty: the restricted target is zero. If sigma.I is empty, its epimorphism
already forces the target to vanish, so again S empty works. There is no point
x to consider if K is empty. No quasi-coherence or finite presentation is used.
-/
theorem exists_finset_generatingSections_near_point
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over K).IsFiniteType] (σ : (H.over V).GeneratingSections) (x : K) :
    ∃ (U : X.Opens) (hUK : U ≤ K), (x : X) ∈ U ∧ ∃ S : Finset σ.I,
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (hUK.trans hKV))).map
          (SheafOfModules.freeMap (R := (moduleRings X.toRingedSpace).over V)
            ((↑) : S → σ.I) ≫ σ.π)) := by
  obtain ⟨U, hUK, hxU, n, l, hl⟩ := exists_finite_free_local_lift X V K hKV H
    (free (R := (moduleRings X.toRingedSpace).over V) σ.I) σ.π x
  obtain ⟨W, hWU, hxW, S, a, ha⟩ := exists_finite_free_local_support X V U
    (hUK.trans hKV) σ.I n l ⟨x.val, hxU⟩
  refine ⟨W, hWU.trans hUK, hxW, S, ?_⟩
  exact epi_overMap_of_factorization (moduleRings X.toRingedSpace) (hUK.trans hKV) hWU
    (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → σ.I)) σ.π l a ha

end AlgebraicGeometry.Scheme.Modules
