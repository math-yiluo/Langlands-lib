import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Artinian.Ring

/-! # Local maps factoring through a locally Artinian closed subscheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ArtinianLocusStalk

/-- A local homomorphism of local rings maps the `c`-th power of the maximal ideal into the
`c`-th power of the maximal ideal. -/
lemma map_mem_maximalIdeal_pow {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (ψ : R →+* S) [IsLocalHom ψ] (c : ℕ) {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R ^ c) :
    ψ a ∈ IsLocalRing.maximalIdeal S ^ c := by
  have h : ψ a ∈ (IsLocalRing.maximalIdeal R ^ c).map ψ := Ideal.mem_map_of_mem ψ ha
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ψ) c h

/-- Every stalk of a locally Artinian scheme is an Artinian ring. -/
lemma isArtinianRing_stalk (Z : Scheme.{u}) [IsLocallyArtinian Z] (z : Z) :
    IsArtinianRing (Z.presheaf.stalk z) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ z) isOpen_univ
  have : IsArtinianRing Γ(Z, U) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨U, hU⟩
  let := Z.presheaf.algebra_section_stalk ⟨z, hzU⟩
  have := hU.isLocalization_stalk ⟨z, hzU⟩
  exact IsArtinianRing.localization_artinian
    (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl (Z.presheaf.stalk z)

/-- The maximal ideal of every stalk of a locally Artinian scheme is nilpotent. -/
lemma exists_maximalIdeal_pow_eq_bot (Z : Scheme.{u}) [IsLocallyArtinian Z] (z : Z) :
    ∃ c : ℕ, IsLocalRing.maximalIdeal (Z.presheaf.stalk z) ^ c = ⊥ := by
  have := isArtinianRing_stalk Z z
  obtain ⟨c, hc⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Z.presheaf.stalk z)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact hc

/-- Over a fixed point of the ambient scheme, the stalks of a locally Artinian closed
subscheme have a common nilpotency exponent. -/
lemma exists_uniform_pow_eq_bot {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    [IsLocallyArtinian Z] (x : X) :
    ∃ c : ℕ, ∀ z : Z, j z = x → IsLocalRing.maximalIdeal (Z.presheaf.stalk z) ^ c = ⊥ := by
  by_cases h : ∃ z : Z, j z = x
  · obtain ⟨z, hz⟩ := h
    obtain ⟨c, hc⟩ := exists_maximalIdeal_pow_eq_bot Z z
    refine ⟨c, fun z' hz' ↦ ?_⟩
    have : z' = z := j.isClosedEmbedding.injective (hz'.trans hz.symm)
    subst this
    exact hc
  · exact ⟨0, fun z hz ↦ (h ⟨z, hz⟩).elim⟩

/-- If a local map out of the stalk at `x` defines a morphism `Spec R ⟶ X` that factors through
`j : Z ⟶ X`, and the maximal ideals of the stalks of `Z` over `x` have vanishing `c`-th
powers, then the map kills the `c`-th power of the maximal ideal at `x`. -/
theorem map_eq_zero_of_factor {X Z : Scheme.{u}} (j : Z ⟶ X) (c : ℕ) (x : X)
    (hc : ∀ z : Z, j z = x → IsLocalRing.maximalIdeal (Z.presheaf.stalk z) ^ c = ⊥)
    {R : CommRingCat.{u}} [IsLocalRing R] (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom]
    (g : Spec R ⟶ Z) (hg : g ≫ j = Spec.map φ ≫ X.fromSpecStalk x)
    (a : X.presheaf.stalk x) (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ c) :
    φ.hom a = 0 := by
  have h₀ : SpecToEquivOfLocalRing X R (g ≫ j) = ⟨x, φ, inferInstance⟩ := by
    rw [hg]
    exact (SpecToEquivOfLocalRing X R).right_inv ⟨x, φ, inferInstance⟩
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp h₀
  simp only [SpecToEquivOfLocalRing_apply_fst, SpecToEquivOfLocalRing_apply_snd_coe] at h₁ h₂
  let ρ := X.presheaf.stalkCongr (by rw [h₁] : Inseparable ((g ≫ j) (IsLocalRing.closedPoint R)) x)
  have hρ : ρ.hom ≫ φ = Scheme.stalkClosedPointTo (g ≫ j) := h₂.symm
  have hz : j (g (IsLocalRing.closedPoint R)) = x := h₁
  have ha' : ρ.inv.hom a ∈ IsLocalRing.maximalIdeal _ ^ c := by
    have : IsLocalHom ρ.inv.hom := isLocalHom_of_isIso ρ.inv
    exact map_mem_maximalIdeal_pow ρ.inv.hom c ha
  have hb : (j.stalkMap (g (IsLocalRing.closedPoint R))).hom (ρ.inv.hom a) = 0 := by
    have := map_mem_maximalIdeal_pow (j.stalkMap (g (IsLocalRing.closedPoint R))).hom c ha'
    rw [hc _ hz] at this
    exact (Submodule.mem_bot _).mp this
  have e₁ : ρ.hom.hom (ρ.inv.hom a) = a :=
    congrArg (fun h : X.presheaf.stalk x ⟶ X.presheaf.stalk x ↦ h.hom a) ρ.inv_hom_id
  have e₂ : φ.hom (ρ.hom.hom (ρ.inv.hom a)) =
      (Scheme.stalkClosedPointTo (g ≫ j)).hom (ρ.inv.hom a) :=
    congrArg (fun h ↦ h.hom (ρ.inv.hom a)) hρ
  have e₃ : (Scheme.stalkClosedPointTo (g ≫ j)).hom (ρ.inv.hom a) =
      (Scheme.stalkClosedPointTo g).hom
        ((j.stalkMap (g (IsLocalRing.closedPoint R))).hom (ρ.inv.hom a)) :=
    congrArg (fun h ↦ h.hom (ρ.inv.hom a)) (Scheme.stalkClosedPointTo_comp g j)
  rw [← e₁, e₂, e₃, hb, map_zero]

end Langlands.AlgebraicGeometry.ArtinianLocusStalk
