import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # The canonical affinization over an affine principal open -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- If a principal open in a qcqs scheme is affine, the canonical affinization map is an
isomorphism over the corresponding principal open of its spectrum of global functions. -/
theorem isIso_toSpecΓ_restrict_basicOpen (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤))
    (hf : IsAffineOpen (X.basicOpen f)) :
    IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f) := by
  let U := X.basicOpen f
  let D : (Spec Γ(X, ⊤)).Opens := PrimeSpectrum.basicOpen f
  let σ := Spec.map (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ f
  have hσ : IsOpenImmersion σ := IsOpenImmersion.of_isLocalization f
  have hU : IsIso U.toSpecΓ := inferInstanceAs (IsIso hf.isoSpec.hom)
  have hcomp : IsOpenImmersion (U.ι ≫ X.toSpecΓ) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
    exact MorphismProperty.comp_mem _ U.toSpecΓ σ inferInstance inferInstance
  have hcomp' :
      IsOpenImmersion ((X.toSpecΓ ∣_ D) ≫ D.ι) := by
    rw [morphismRestrict_ι]
    dsimp [D]
    rw [X.toSpecΓ_preimage_basicOpen]
    exact hcomp
  have hrest : IsOpenImmersion (X.toSpecΓ ∣_ D) := .of_comp _ D.ι
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨hrest, (TopCat.epi_iff_surjective _).mpr ?_⟩
  intro y
  obtain ⟨z, hz⟩ : ∃ z, σ z = y.1 := by
    change y.1 ∈ Set.range (PrimeSpectrum.comap
      (algebraMap Γ(X, ⊤) Γ(X, U)))
    rw [PrimeSpectrum.localization_away_comap_range _ f]
    exact y.2
  obtain ⟨x, hx⟩ := (TopCat.epi_iff_surjective U.toSpecΓ.base).mp inferInstance z
  have hxy : X.toSpecΓ x.1 = y.1 := by
    rw [← hz, ← hx]
    exact (congrArg (fun k : U.toScheme ⟶ Spec Γ(X, ⊤) => k x)
      (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top U)).symm
  refine ⟨⟨x.1, ?_⟩, ?_⟩
  · change X.toSpecΓ x.1 ∈ D
    rw [hxy]
    exact y.2
  · apply Subtype.ext
    exact (morphismRestrict_base_coe X.toSpecΓ D _).trans hxy

/-- The isomorphism furnished by an affine principal open of a qcqs scheme. Its forward
map is the restriction of the canonical affinization map. -/
def affinizationBasicOpenIso (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Γ(X, ⊤)) (hf : IsAffineOpen (X.basicOpen f)) :
    (X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen f).toScheme ≅
      Scheme.Opens.toScheme (X := Spec Γ(X, ⊤)) (PrimeSpectrum.basicOpen f) :=
  letI := isIso_toSpecΓ_restrict_basicOpen X f hf
  asIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f)

end Langlands.AlgebraicGeometry
