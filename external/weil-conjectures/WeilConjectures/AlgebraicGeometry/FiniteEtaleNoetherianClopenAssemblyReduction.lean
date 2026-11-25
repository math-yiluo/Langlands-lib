/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Transport of a finite stratification along a surjective closed immersion. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Transport reduced strata along a surjective closed immersion.
Source: Stacks Project, Tag 01J3.
(blueprint: lem-a1-finite-etale-noetherian-clopen-assembly-reduction).

Proof: keep the domains and compose every stratum immersion with r; a composite of
immersions is an immersion, so its range is locally closed. Since r is injective, the
images of disjoint strata are disjoint, and since r is surjective the images cover Y.
Reducedness of the domains and the property P are unchanged.
-/
theorem transport_reduced_stratification_along_surjective_closed_immersion
    {X Y : Scheme.{u}} (r : X ⟶ Y) [IsClosedImmersion r]
    (hrange : Set.range r = (Set.univ : Set Y))
    (P : (B : Scheme.{u}) → (B ⟶ Y) → Prop)
    (T : FiniteLocallyClosedStratification X)
    (hT : ∀ a : Fin T.n, IsReduced (T.domain a))
    (hP : ∀ a : Fin T.n, P (T.domain a) (T.immersion a ≫ r)) :
    ∃ S : FiniteLocallyClosedStratification Y,
      (∀ a : Fin S.n, IsReduced (S.domain a)) ∧
      ∀ a : Fin S.n, P (S.domain a) (S.immersion a) := by
  let S : FiniteLocallyClosedStratification Y :=
    { n := T.n
      stratum := fun a => Set.range (T.immersion a ≫ r)
      isLocallyClosed_stratum := fun a => by
        have h := T.isImmersion a
        exact (T.immersion a ≫ r).isLocallyClosed_range
      iUnion_stratum_eq_univ := by
        apply Set.eq_univ_of_forall
        intro y
        obtain ⟨x, rfl⟩ := hrange.symm ▸ Set.mem_univ y
        have hx : x ∈ ⋃ a, T.stratum a :=
          T.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
        rw [← T.range_immersion a] at ha
        obtain ⟨z, rfl⟩ := ha
        exact Set.mem_iUnion.mpr ⟨a, ⟨z, rfl⟩⟩
      pairwise_disjoint_stratum := by
        intro a b hab
        apply Set.disjoint_left.mpr
        rintro y hx hy
        obtain ⟨x, hx⟩ := hx
        obtain ⟨z, hz⟩ := hy
        have hxz : T.immersion a x = T.immersion b z := by
          apply r.isClosedEmbedding.injective
          simpa only [Scheme.Hom.comp_apply] using hx.trans hz.symm
        have hax : T.immersion a x ∈ T.stratum a := by
          rw [← T.range_immersion a]
          exact ⟨x, rfl⟩
        have hbz : T.immersion a x ∈ T.stratum b := by
          rw [← T.range_immersion b]
          exact ⟨z, hxz.symm⟩
        exact Set.disjoint_left.mp (T.pairwise_disjoint_stratum hab) hax hbz
      domain := T.domain
      immersion := fun a => T.immersion a ≫ r
      isImmersion := fun a => by
        have h := T.isImmersion a
        infer_instance
      range_immersion := fun a => rfl }
  refine ⟨S, hT, ?_⟩
  intro a
  exact hP a

end AlgebraicGeometry.Scheme
