import Langlands.Geometry.Building.AffineChamberWallComparisonProof

/-! # Signs on the chamber across a simple wall -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {C : Set A} {ψ : A →ᵃ[ℝ] ℝ} {v : V}

/-- The positivity assertion for every simple wall in the given real affine torsor. -/
def SimpleReflectionPositivityStatement : Prop :=
  ∀ (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) (ψ : A →ᵃ[ℝ] ℝ),
    ψ ∈ simpleAffineRoots Ψ C →
    ∀ (v : V) (hv : IsCoroot Ψ ψ v) (η : A →ᵃ[ℝ] ℝ),
      η ∈ positiveRoots Ψ C →
      (¬ ∃ c : ℝ, η = c • ψ) →
        η ∈ positiveRoots Ψ (affineReflection ψ hv.1 '' C)

/-- A geometric chamber wall has a point in the sign closure of the chamber
at which every root vanishing there is proportional to the wall root. -/
theorem exists_wall_point_of_mem_simpleAffineRoots
    (hψ : ψ ∈ simpleAffineRoots Ψ C) (hv : IsCoroot Ψ ψ v) :
    ∃ y : A, ψ y = 0 ∧
      (∀ x ∈ C, y ∈ facetClosure Ψ x) ∧
      ∀ η ∈ Ψ, η y = 0 → ∃ c : ℝ, η = c • ψ := by
  obtain ⟨Fa, ⟨⟨y, rfl⟩, x₀, hx₀, hFa⟩, hspan⟩ := hψ.2.2.2.2
  have hyH : y ∈ hyperplane ψ :=
    hspan ▸ subset_affineSpan ℝ _ (mem_facet_self Ψ y)
  refine ⟨y, hyH, ?_, ?_⟩
  · intro x hx
    have hrel : facetRel Ψ x₀ x := by
      rw [← hx₀] at hx
      exact hx
    rw [← facetClosure_eq_of_facetRel hrel]
    exact hFa (mem_facet_self Ψ y)
  · intro η hη hηy
    have hle : hyperplane ψ ≤ hyperplane η := by
      rw [← hspan]
      exact affineSpan_le.2 (facet_subset_hyperplane ⟨hη, hηy⟩)
    exact ⟨η.linear v / 2, eq_smul_of_hyperplane_le hv.1 hle⟩

/-- A simple reflection preserves the sign of every root not proportional
to its wall root, throughout its chamber. -/
theorem sign_reflection_eq_of_mem_simpleAffineRoots
    (hψ : ψ ∈ simpleAffineRoots Ψ C) (hv : IsCoroot Ψ ψ v)
    {η : A →ᵃ[ℝ] ℝ} (hη : η ∈ Ψ)
    (hηψ : ¬ ∃ c : ℝ, η = c • ψ) {x : A} (hx : x ∈ C) :
    SignType.sign (η (affineReflection ψ hv.1 x)) = SignType.sign (η x) := by
  obtain ⟨y, hy, hcl, hprop⟩ := exists_wall_point_of_mem_simpleAffineRoots hψ hv
  have hηy : η y ≠ 0 := fun h => hηψ (hprop η hη h)
  have hηr : η.comp (affineReflection ψ hv.1 : A →ᵃ[ℝ] A) ∈ Ψ := by
    rw [comp_affineReflection]
    exact hv.2 η hη
  have h1 : SignType.sign (η y) = SignType.sign (η x) :=
    (hcl x hx η hη).resolve_left (sign_ne_zero.2 hηy)
  have h2 := hcl x hx _ hηr
  have hry : affineReflection ψ hv.1 y = y := affineReflection_apply_of_mem ψ hv.1 hy
  change SignType.sign (η (affineReflection ψ hv.1 y)) = 0 ∨
    SignType.sign (η (affineReflection ψ hv.1 y)) =
      SignType.sign (η (affineReflection ψ hv.1 x)) at h2
  rw [hry] at h2
  exact (h2.resolve_left (sign_ne_zero.2 hηy)).symm.trans h1

/-- The positive roots not proportional to a chamber-simple root remain
positive on the reflected chamber. -/
theorem mem_positiveRoots_reflected_chamber
    (hψ : ψ ∈ simpleAffineRoots Ψ C) (hv : IsCoroot Ψ ψ v)
    {η : A →ᵃ[ℝ] ℝ} (hη : η ∈ positiveRoots Ψ C)
    (hηψ : ¬ ∃ c : ℝ, η = c • ψ) :
    η ∈ positiveRoots Ψ (affineReflection ψ hv.1 '' C) := by
  refine ⟨hη.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← sign_eq_one_iff,
    sign_reflection_eq_of_mem_simpleAffineRoots hψ hv hη.1 hηψ hx]
  exact sign_pos (hη.2 x hx)

/-- The positivity statement follows from the wall-face sign argument. -/
theorem simpleReflectionPositivity :
    SimpleReflectionPositivityStatement (V := V) (A := A) := by
  intro Ψ C ψ hψ v hv η hη hηψ
  exact mem_positiveRoots_reflected_chamber hψ hv hη hηψ

end Langlands.Geometry.Building.AffineRootSystem
