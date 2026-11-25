/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import all WeilConjectures.AlgebraicGeometry.AmpleIso

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.IsAffineOfFiniteClosedCover
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes

/-! # Affineness of a compatible component section locus

Source: Stacks Project, Varieties Lemma 09NX, second paragraph;
Limits Lemma 09NL and Properties Section 01PR.
(blueprint: lem-sc-affine-locus-compatible-component-sections).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules


/-- A fixed global section with affine component loci has affine locus, and contains
any set whose inverse images lie in those loci.

Source: Stacks Project, Varieties Lemma 09NX, second paragraph;
Limits Lemma 09NL and Properties Section 01PR.
(blueprint: lem-sc-affine-locus-compatible-component-sections).

Proof: let W be the nonvanishing locus of t. It is open because L is invertible:
in a local frame it is the basic open of the section coefficient. At a component
point, the adjunction unit identifies the pulled-back fibre value with one tensor
the value of t. The residue-field map is injective, so extension of this rank-one
vector space preserves and reflects nonzero values. Each e a preserves nonvanishing,
and the section compatibility identifies the inverse image of W with V a.
For x in T choose a component point y over it by hcover. The containment hypothesis
makes s a nonvanishing at y, and the fibre calculation puts x in W. The restricted
closed immersions (V a).toScheme → W.toScheme form a finite closed cover. Their
sources are affine by hVaff. Apply isAffine_of_finite_closed_cover, including its
empty-cover case, to conclude that W is affine. Finally transport t along the inverse
right unitor L ≅ L.tensorPow 1; a module isomorphism preserves the maximal ideal
times each stalk and hence the nonvanishing locus. The transported section q has
locus W, giving the stated witnesses. Neither reducedness nor finiteness or closedness
of T is needed for this argument: all gluing is already supplied as input.
-/
theorem affine_locus_of_compatible_component_sections
    (X : Scheme.{u}) (r : ℕ) (C : Fin r → Scheme.{u})
    (i : ∀ a, C a ⟶ X) [∀ a, IsClosedImmersion (i a)]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ) (T : Set X)
    (L : X.Modules) [L.IsInvertible] (t : Γ(L, ⊤))
    (P : ∀ a, (C a).Modules) [∀ a, (P a).IsInvertible]
    (s : ∀ a, Γ(P a, ⊤)) (V : ∀ a, (C a).Opens)
    (hTV : ∀ a, i a ⁻¹' T ⊆ nonvanishingLocus (P a) (s a))
    (hVlocus : ∀ a, (V a : Set (C a)) = nonvanishingLocus (P a) (s a))
    (hVaff : ∀ a, IsAffineOpen (V a))
    (he : ∀ a, ∃ e : (tensorPullback (i a)).obj L ≅ P a,
      e.hom.val.app (op ⊤)
        (((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app L).val.app
          (op ⊤) t) = s a) :
    ∃ (q : (L.tensorPow 1).val.presheaf.obj (op ⊤)) (U : X.Opens),
      T ⊆ (U : Set X) ∧ IsAffineOpen U ∧
        (U : Set X) = nonvanishingLocus (L.tensorPow 1) q  := by
  classical
  obtain ⟨U, hUlocus, _, _⟩ := nonvanishing_section_trivializes X L t
  have hpoint (a : Fin r) (x : C a) : i a x ∈ U ↔ x ∈ V a := by
    obtain ⟨e, heq⟩ := he a
    let res : Γ((tensorPullback (i a)).obj L, ⊤) :=
      (((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app L).val.app
        (op ⊤) t)
    have : ((tensorPullback (i a)).obj L).IsInvertible := IsInvertible.of_iso e.symm
    have hxres : x ∈ nonvanishingLocus ((tensorPullback (i a)).obj L) res ↔
        i a x ∈ nonvanishingLocus L t := by
      exact nonvanishing_tensorPullback (i a) L t x
    have hiso := Set.ext_iff.mp (nonvanishingLocus_iso e res) x
    change e.hom.app ⊤ res = s a at heq
    rw [heq] at hiso
    have hU := Set.ext_iff.mp hUlocus (i a x)
    have hV := Set.ext_iff.mp (hVlocus a) x
    exact hU.trans (hxres.symm.trans (hiso.symm.trans hV.symm))
  have hpre (a : Fin r) : i a ⁻¹ᵁ U = V a := by
    ext x
    exact hpoint a x
  have hTU : T ⊆ (U : Set X) := by
    intro x hx
    obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    exact (hpoint a y).2 ((Set.ext_iff.mp (hVlocus a) y).mpr (hTV a hx))
  have hUaff : IsAffineOpen U := by
    have (a : Fin r) : IsAffine (i a ⁻¹ᵁ U).toScheme := hpre a ▸ hVaff a
    have (a : Fin r) : IsClosedImmersion ((i a) ∣_ U) := inferInstance
    exact isAffine_of_finite_closed_cover U.toScheme r
      (fun a ↦ (i a ⁻¹ᵁ U).toScheme) (fun a ↦ (i a) ∣_ U) (by
        intro x
        obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x.1)
        refine ⟨a, ⟨y, ?_⟩, ?_⟩
        · change i a y ∈ U
          rw [hy]
          exact x.2
        · apply Subtype.ext
          simpa using hy)
  let e : L.tensorPow 1 ≅ L := rightUnitor L
  let q := e.inv.app ⊤ t
  refine ⟨q, U, hTU, hUaff, ?_⟩
  exact hUlocus.trans (nonvanishingLocus_iso e.symm t).symm

end AlgebraicGeometry.Scheme.Modules
