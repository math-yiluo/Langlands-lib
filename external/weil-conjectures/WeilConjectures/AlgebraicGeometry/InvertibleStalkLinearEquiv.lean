/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
import all WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes

/-! # The stalk of an invertible module has rank one

Source: Stacks Project, Modules, Lemma 01CY, proof.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Local triviality of an invertible module gives a rank-one trivialization of each stalk.

Source: Stacks Project, Modules, Lemma 01CY, proof.
(blueprint: lem-weil-pbc-invertible-stalk-linear-equiv).

Proof: Trivialize L on an open neighbourhood U of y. The restriction isomorphism
carries the unit free generator to a section t which freely generates L on every
smaller open. The linear map a ↦ a • germ(t) is surjective because every module germ
has a representative on a neighbourhood inside U, where t generates. It is injective
because equality of germs gives equality on a common smaller neighbourhood, where
scalar multiplication by the restricted generator is injective. Its inverse gives the
asserted linear equivalence. The assertion is vacuous on an empty scheme. -/
theorem invertible_stalk_linearEquiv (Y : Scheme.{u}) (L : Y.Modules)
    [L.IsInvertible] (y : Y) :
    Nonempty (↑(TopCat.Presheaf.stalk L.val.presheaf y) ≃ₗ[Y.presheaf.stalk y]
      ↑(Y.presheaf.stalk y)) := by
  obtain ⟨U, hy, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := L) y
  let e' : L.restrict U.ι ≅ Modules.unit U :=
    (restrictFunctorIsoPullback U.ι).app L ≪≫ e
  have ht' := (isFreeGenerator_one (⊤ : U.toScheme.Opens)).app_hom e'.symm
  obtain ⟨t, ht⟩ : ∃ t : Γ(L, U), IsFreeGenerator t :=
    ⟨_, ((isFreeGenerator_restrict_iff U.ι L _).mp ht').map
      (Scheme.Opens.ι_image_top U).ge⟩
  let f := LinearMap.toSpanSingleton (Y.presheaf.stalk y)
    (L.presheaf.stalk y) (L.presheaf.germ U y hy t)
  have hf : Function.Bijective f := stalk_generator_bijective ht y hy
  exact ⟨(LinearEquiv.ofBijective f hf).symm⟩

end AlgebraicGeometry.Scheme.Modules
