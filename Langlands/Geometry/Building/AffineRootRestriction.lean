import Langlands.Geometry.Building.AffineRootSystem

/-! # Nonconstant restrictions of affine roots -/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA uW uB

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {W : Type uW} {B : Type uB}
  [AddCommGroup W] [Module ℝ W] [AddTorsor W B]

/-- Restrict an affine root arrangement along an affine map, discarding
the roots whose restrictions have zero derivative. -/
def restrictedRoots (f : A →ᵃ[ℝ] B) (Ψ : Set (B →ᵃ[ℝ] ℝ)) :
    Set (A →ᵃ[ℝ] ℝ) :=
  {φ | ∃ ψ ∈ Ψ, ψ.comp f = φ ∧ φ.linear ≠ 0}

theorem mem_restrictedRoots {f : A →ᵃ[ℝ] B} {Ψ : Set (B →ᵃ[ℝ] ℝ)}
    {φ : A →ᵃ[ℝ] ℝ} :
    φ ∈ restrictedRoots f Ψ ↔ ∃ ψ ∈ Ψ, ψ.comp f = φ ∧ φ.linear ≠ 0 :=
  Iff.rfl

theorem linear_ne_zero_of_mem_restrictedRoots
    {f : A →ᵃ[ℝ] B} {Ψ : Set (B →ᵃ[ℝ] ℝ)}
    {φ : A →ᵃ[ℝ] ℝ} (hφ : φ ∈ restrictedRoots f Ψ) : φ.linear ≠ 0 := by
  obtain ⟨ψ, hψ, rfl, hφ⟩ := hφ
  exact hφ

/-- Roots constant on the image impose no additional sign condition, so the
restricted arrangement has precisely the pulled-back facet relation. -/
theorem facetRel_restrictedRoots_iff (f : A →ᵃ[ℝ] B)
    (Ψ : Set (B →ᵃ[ℝ] ℝ)) (x y : A) :
    facetRel (restrictedRoots f Ψ) x y ↔ facetRel Ψ (f x) (f y) := by
  constructor
  · intro h ψ hψ
    by_cases hzero : (ψ.comp f).linear = 0
    · obtain ⟨c, hc⟩ := (ψ.comp f).linear_eq_zero_iff_exists_const.mp hzero
      have hx := congrArg (fun φ : A →ᵃ[ℝ] ℝ => φ x) hc
      have hy := congrArg (fun φ : A →ᵃ[ℝ] ℝ => φ y) hc
      change SignType.sign ((ψ.comp f) x) = SignType.sign ((ψ.comp f) y)
      rw [hx, hy]
      rfl
    · exact h (ψ.comp f) ⟨ψ, hψ, rfl, hzero⟩
  · rintro h _ ⟨ψ, hψ, rfl, -⟩
    exact h ψ hψ

/-- A restricted facet is exactly the preimage of the ambient facet, even
when the affine map is not surjective or injective. -/
theorem facet_restrictedRoots_eq_preimage (f : A →ᵃ[ℝ] B)
    (Ψ : Set (B →ᵃ[ℝ] ℝ)) (x : A) :
    facet (restrictedRoots f Ψ) x = f ⁻¹' facet Ψ (f x) := by
  ext y
  exact facetRel_restrictedRoots_iff f Ψ x y

/-- An affine embedding reflects an ambient vertex for the restricted
arrangement; no affine-root-system axioms are required. -/
theorem isVertex_restrictedRoots_of_isVertex (f : A →ᵃ[ℝ] B)
    (hf : Function.Injective f) (Ψ : Set (B →ᵃ[ℝ] ℝ)) {x : A}
    (hx : IsVertex Ψ (f x)) : IsVertex (restrictedRoots f Ψ) x := by
  change facet (restrictedRoots f Ψ) x = {x}
  rw [facet_restrictedRoots_eq_preimage, hx]
  ext y
  exact hf.eq_iff

private theorem ker_comp_eq_of_ker_eq (f : A →ᵃ[ℝ] B)
    {ψ ψ' : B →ᵃ[ℝ] ℝ}
    (h : LinearMap.ker ψ.linear = LinearMap.ker ψ'.linear) :
    LinearMap.ker (ψ.comp f).linear = LinearMap.ker (ψ'.comp f).linear := by
  change LinearMap.ker (ψ.linear.comp f.linear) =
    LinearMap.ker (ψ'.linear.comp f.linear)
  rw [LinearMap.ker_comp, LinearMap.ker_comp, h]

/-- Special points descend along nonconstant affine-root restriction. The
parallel ambient vanishing root still has nonzero restriction because its
restricted derivative has the same kernel as the given restricted root. -/
theorem isSpecialPoint_restrictedRoots_of_isSpecialPoint (f : A →ᵃ[ℝ] B)
    (Ψ : Set (B →ᵃ[ℝ] ℝ)) (hΨ : ∀ ψ ∈ Ψ, ψ.linear ≠ 0)
    {x : A} (hx : IsSpecialPoint Ψ (f x)) :
    IsSpecialPoint (restrictedRoots f Ψ) x := by
  apply (isSpecialPoint_iff_ker
    (fun _ hφ => linear_ne_zero_of_mem_restrictedRoots hφ) x).mpr
  rintro _ ⟨ψ, hψ, rfl, hnonzero⟩
  obtain ⟨ψ', hψ', hker⟩ := (isSpecialPoint_iff_ker hΨ (f x)).mp hx ψ hψ
  have hker' := ker_comp_eq_of_ker_eq f hker
  have hnonzero' : (ψ'.comp f).linear ≠ 0 := by
    intro hzero
    apply hnonzero
    apply LinearMap.ker_eq_top.mp
    rw [hker', hzero, LinearMap.ker_zero]
  exact ⟨ψ'.comp f, ⟨⟨ψ', hψ'.1, rfl, hnonzero'⟩, hψ'.2⟩, hker'⟩

/-- An explicit identity of the actual root arrangements suffices for
specialness of a preimage point. -/
theorem isSpecialPoint_of_restrictedRoots_eq (f : A →ᵃ[ℝ] B)
    {Φ : Set (A →ᵃ[ℝ] ℝ)} {Ψ : Set (B →ᵃ[ℝ] ℝ)}
    (hroots : restrictedRoots f Ψ = Φ)
    (hΨ : ∀ ψ ∈ Ψ, ψ.linear ≠ 0)
    {x : A} (hx : IsSpecialPoint Ψ (f x)) : IsSpecialPoint Φ x := by
  rw [← hroots]
  exact isSpecialPoint_restrictedRoots_of_isSpecialPoint f Ψ hΨ hx

end Langlands.Geometry.Building.AffineRootSystem
