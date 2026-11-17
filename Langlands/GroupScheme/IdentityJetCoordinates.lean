import Langlands.GroupScheme.IdentityJetSheaf

/-! # Actual identity-jet sections from affine ambient coordinates -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S) {B : CommRingCat.{u}}
  (j : G.X.left ⟶ Spec B)

/-- Restriction of an actual ambient affine coordinate above a base open. -/
def coordinateMap (U : S.Opens) : B →+* Γ(G.X.left, G.X.hom ⁻¹ᵁ U) :=
  (j.appLE ⊤ (G.X.hom ⁻¹ᵁ U) (by simp)).hom.comp (Scheme.ΓSpecIso B).inv.hom

/-- Restriction of an ambient coordinate to the actual identity jet. -/
def jetCoordinateMap (n : ℕ) (U : S.Opens) :
    B →+* Γ(scheme G n, projection G n ⁻¹ᵁ U) :=
  ((inclusion G n ≫ j).appLE ⊤ (projection G n ⁻¹ᵁ U) (by simp)).hom.comp
    (Scheme.ΓSpecIso B).inv.hom

@[simp]
theorem jetCoordinateMap_eq (n : ℕ) (U : S.Opens) (b : B) :
    jetCoordinateMap G j n U b =
      (inclusion G n).app (G.X.hom ⁻¹ᵁ U) (coordinateMap G j U b) := by
  have h := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE (inclusion G n) j ⊤ (G.X.hom ⁻¹ᵁ U)
      (projection G n ⁻¹ᵁ U) (by simp) le_rfl) ((Scheme.ΓSpecIso B).inv b)
  change (j.appLE ⊤ (G.X.hom ⁻¹ᵁ U) (by simp) ≫
    (inclusion G n).appLE (G.X.hom ⁻¹ᵁ U)
      ((inclusion G n) ⁻¹ᵁ (G.X.hom ⁻¹ᵁ U)) le_rfl)
    ((Scheme.ΓSpecIso B).inv b) = _ at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h.symm

@[simp]
theorem jetCoordinateMap_restrict (n : ℕ) {U V : S.Opens} (h : V ≤ U) (b : B) :
    (module G n).presheaf.map (homOfLE h).op (jetCoordinateMap G j n U b) =
      jetCoordinateMap G j n V b := by
  change (scheme G n).presheaf.map
    ((TopologicalSpace.Opens.map (projection G n).base).map (homOfLE h)).op
      (jetCoordinateMap G j n U b) = _
  exact ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_map (inclusion G n ≫ j) (by simp)
      ((TopologicalSpace.Opens.map (projection G n).base).map (homOfLE h)).op)
    ((Scheme.ΓSpecIso B).inv b)

/-- An ideal of ambient functions vanishing on the actual identity image. -/
def VanishesAtIdentity (I : Ideal B) : Prop :=
  ∀ b ∈ I, (G.identitySection ≫ j).appTop ((Scheme.ΓSpecIso B).inv b) = 0

/-- Identity vanishing remains true after restricting to any affine base open. -/
theorem augmentation_coordinateMap_eq_zero (I : Ideal B) (hI : VanishesAtIdentity G j I)
    (U : S.affineOpens) {b : B} (hb : b ∈ I) :
    augmentation G U (coordinateMap G j U b) = 0 := by
  have h := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE G.identitySection j ⊤ (G.X.hom ⁻¹ᵁ U)
      U (by simp) (le_of_eq (identity_preimage G U).symm)) ((Scheme.ΓSpecIso B).inv b)
  change (G.identitySection.appLE (G.X.hom ⁻¹ᵁ U) U
    (le_of_eq (identity_preimage G U).symm)) (coordinateMap G j U b) = 0
  rw [show (G.identitySection.appLE (G.X.hom ⁻¹ᵁ U) U
      (le_of_eq (identity_preimage G U).symm)) (coordinateMap G j U b) =
      (G.identitySection ≫ j).appLE ⊤ U (by simp) ((Scheme.ΓSpecIso B).inv b) from h]
  change S.presheaf.map (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
    ((G.identitySection ≫ j).appTop ((Scheme.ΓSpecIso B).inv b)) = 0
  rw [hI b hb, map_zero]

variable [IsAffineHom G.X.hom]

/-- Ambient identity ideal powers vanish on the corresponding actual jet. -/
theorem jetCoordinateMap_eq_zero (I : Ideal B) (hI : VanishesAtIdentity G j I)
    (n : ℕ) {b : B} (hb : b ∈ I ^ (n + 1)) :
    jetCoordinateMap G j n ⊤ b = 0 := by
  refine (module G n).isSheaf.section_ext (U := op ⊤) ?_
  intro x hx
  obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨U, hle, hxU, ?_⟩
  rw [jetCoordinateMap_restrict, map_zero]
  apply (sectionsRingEquiv G n ⟨U, hU⟩).injective
  rw [jetCoordinateMap_eq, sectionsRingEquiv_inclusion_app, map_zero]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hker : I ≤ (RingHom.ker (augmentation G U)).comap (coordinateMap G j U) :=
    fun a ha => augmentation_coordinateMap_eq_zero G j I hI ⟨U, hU⟩ ha
  have hmap : I.map (coordinateMap G j U) ≤ RingHom.ker (augmentation G U) :=
    Ideal.map_le_iff_le_comap.mpr hker
  have hp := pow_le_pow_left' hmap (n + 1)
  rw [← Ideal.map_pow] at hp
  exact hp (Ideal.mem_map_of_mem (coordinateMap G j U) hb)

/-- Actual global jet sections supplied by the fixed ambient truncated coordinates. -/
def quotientCoordinates (I : Ideal B) (hI : VanishesAtIdentity G j I) (n : ℕ) :
    (B ⧸ I ^ (n + 1)) →+* Γ(scheme G n, projection G n ⁻¹ᵁ ⊤) :=
  Ideal.Quotient.lift _ (jetCoordinateMap G j n ⊤)
    (fun _b hb => jetCoordinateMap_eq_zero G j I hI n hb)

@[simp]
theorem quotientCoordinates_mk (I : Ideal B) (hI : VanishesAtIdentity G j I)
    (n : ℕ) (b : B) :
    quotientCoordinates G j I hI n (Ideal.Quotient.mk _ b) =
      jetCoordinateMap G j n ⊤ b := rfl

/-- Restrictions of the actual global generators are the same ambient functions
in the affine augmentation quotient. -/
theorem sectionsEquiv_restrict_quotientCoordinates (I : Ideal B)
    (hI : VanishesAtIdentity G j I) (n : ℕ) (U : S.affineOpens) (b : B) :
    sectionsEquiv G n U
      ((module G n).presheaf.map (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
        (quotientCoordinates G j I hI n (Ideal.Quotient.mk _ b))) =
      Ideal.Quotient.mk (RingHom.ker (augmentation G U) ^ (n + 1))
        (coordinateMap G j U b) := by
  rw [quotientCoordinates_mk, jetCoordinateMap_restrict, jetCoordinateMap_eq,
    sectionsEquiv_inclusion_app]

end Langlands.GroupScheme.IdentityJet
