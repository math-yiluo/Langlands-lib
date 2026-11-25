/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Affine opens of schemes over `Spec B`, as `B`-algebras

For a morphism `q : V ⟶ Spec B` and an affine open `W` of `V`, the ring `Γ(V, W)` is a
`B`-algebra via `B ≅ Γ(Spec B, ⊤) ⟶ Γ(V, W)` (`AlgebraicGeometry.IsAffineOpen.ringHomOfSpec`),
and `Spec` of this ring map is `W ⟶ V ⟶ Spec B` (`IsAffineOpen.SpecMap_ringHomOfSpec`). If `q`
is étale, so is the ring map (`IsAffineOpen.etale_ringHomOfSpec`).

We also record that `Spec` of a localization away from `r` has range the basic open of `r`, for
an arbitrary `IsLocalization.Away r S` (`AlgebraicGeometry.opensRange_SpecMap_algebraMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- The range of `Spec S ⟶ Spec R`, for `S` a localization of `R` away from `r`, is the basic
open of `r`. -/
lemma opensRange_SpecMap_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] :
    haveI := IsOpenImmersion.of_isLocalization (S := S) r
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).opensRange = PrimeSpectrum.basicOpen r := by
  have := IsOpenImmersion.of_isLocalization (S := S) r
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range S r

namespace IsAffineOpen

variable {B : Type u} [CommRing B] {V : Scheme.{u}} (q : V ⟶ Spec (.of B)) {W : V.Opens}

/-- The ring map `B ⟶ Γ(V, W)` for `q : V ⟶ Spec B` and an affine open `W ⊆ V`. -/
noncomputable def ringHomOfSpec (_hW : IsAffineOpen W) : B →+* Γ(V, W) :=
  (q.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom

variable (hW : IsAffineOpen W)

/-- `Spec` of the ring map `B ⟶ Γ(V, W)` is the composite `Spec Γ(V, W) ⟶ V ⟶ Spec B`. -/
lemma SpecMap_ringHomOfSpec :
    Spec.map (CommRingCat.ofHom (hW.ringHomOfSpec q)) = hW.fromSpec ≫ q := by
  rw [ringHomOfSpec, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec]

/-- The ring map `B ⟶ Γ(V, W)` is étale if `q` is. -/
lemma etale_ringHomOfSpec [Etale q] : (hW.ringHomOfSpec q).Etale :=
  RingHom.Etale.respectsIso.2 _ (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appLE (P := @Etale) q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩
      le_top)

end IsAffineOpen

end AlgebraicGeometry
