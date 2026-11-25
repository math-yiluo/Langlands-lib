/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
import Mathlib.AlgebraicGeometry.Restrict

/-! Comparison of the two formulations of universal homeomorphisms. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A morphism whose every base change is a homeomorphism is an integral, universally
injective, surjective morphism.
Source: Stacks Project, Tag 04DF, with Tag 05YU.
Proof: Every base change is closed and injective, so the morphism is universally closed
and universally injective, and it is surjective. Transport an affine open cover of the
source along the underlying homeomorphism. The inverse image of each transported open
is the original affine open. The restricted morphism is surjective and universally
closed, so its target is affine by Tag 05YU. Hence these are matching affine covers.
The affine criterion, local on the target, shows that the original morphism is affine.
An affine universally closed morphism is integral by Tag 01WM.
(blueprint: lem-trf-universally-homeomorph-integral) -/
theorem isUniversalHomeomorphism_of_universally_isHomeomorph
    {X Y : Scheme.{u}} (r : X ⟶ Y)
    (hr : (topologically IsHomeomorph).universally r) : IsUniversalHomeomorphism r := by
  have hhome : IsHomeomorph r := hr _ _ _ IsPullback.of_id_snd
  have hclosed : UniversallyClosed r := ⟨by
    intro X' Y' a b f hf
    exact (hr a b f hf).isClosedMap⟩
  have hinj : UniversallyInjective r := ⟨by
    intro X' Y' a b f hf
    exact (hr a b f hf).injective⟩
  have hsurj : Surjective r := ⟨hhome.surjective⟩
  let V (U : X.affineOpens) : Y.Opens :=
    ⟨r '' (U : Set X), hhome.isOpenMap _ U.1.isOpen⟩
  have hpre (U : X.affineOpens) : r ⁻¹ᵁ V U = U.1 := by
    apply Opens.ext
    exact Set.preimage_image_eq _ hhome.injective
  have haffpre (U : X.affineOpens) : IsAffine (r ⁻¹ᵁ V U).toScheme := by
    rw [hpre]
    exact U.2
  have haff (U : X.affineOpens) : IsAffine (V U).toScheme := by
    have := haffpre U
    have : Surjective (r ∣_ V U) :=
      ⟨(hr _ _ _ (isPullback_morphismRestrict r (V U))).surjective⟩
    exact isAffine_of_surjective_of_universallyClosed (r ∣_ V U)
  have hcover : (⨆ U : X.affineOpens, V U) = ⊤ := by
    apply top_unique
    intro y hy
    obtain ⟨x, rfl⟩ := hhome.surjective y
    obtain ⟨W, hW, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    let U : X.affineOpens := ⟨W, hW⟩
    exact Opens.mem_iSup.mpr ⟨U, ⟨x, hx, rfl⟩⟩
  have haffine : IsAffineHom r :=
    HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom)
      (fun U ↦ ⟨V U, haff U⟩) hcover haffpre
  have : IsIntegralHom r :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hclosed, haffine⟩
  exact {}

end AlgebraicGeometry
