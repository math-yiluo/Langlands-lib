import Langlands.Geometry.Building.AffineWeylFacetFixing

/-! # Regular points along invariant affine directions -/

noncomputable section

universe uV uA uI

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- If each root through `p` is nonconstant on a subspace, that subspace contains
a direction from `p` to a regular point whose facet closure contains `p`. -/
theorem IsLocallyFiniteReflectionArrangement.exists_regularPoint_in_subspace
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (p : A) (W : Submodule ℝ V)
    (hW : ∀ ψ ∈ Ψ, ψ p = 0 → ∃ v : W, ψ.linear v ≠ 0) :
    ∃ x : A, IsRegular Ψ x ∧ p ∈ facetClosure Ψ x ∧ (x -ᵥ p : V) ∈ W := by
  classical
  let R : Set (Module.Dual ℝ V) :=
    {a | ∃ ψ ∈ Ψ, ψ p = 0 ∧ ψ.linear = a}
  have hR : R.Finite := hΨ.finite_derivativeRoots.subset (by
    rintro a ⟨ψ, hψ, _, rfl⟩
    exact ⟨ψ, hψ, rfl⟩)
  let : Finite R := hR.to_subtype
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun a : R => (a : Module.Dual ℝ V).comp W.subtype) (by
      rintro ⟨a, ψ, hψ, hp, rfl⟩
      exact hW ψ hψ hp)
  obtain ⟨ε, hε, hsign⟩ := exists_pos_of_eventually
    (eventually_sign_smul_vadd hΨ p (v : V))
  refine ⟨ε • (v : V) +ᵥ p, ?_, ?_, ?_⟩
  · intro ψ hψ
    by_cases hp : ψ p = 0
    · rw [apply_smul_vadd, hp, zero_add]
      exact mul_ne_zero hε.ne' (hv ⟨ψ.linear, ψ, hψ, hp, rfl⟩)
    · intro hz
      have hs := hsign ψ hψ hp
      rw [hz, sign_zero, eq_comm, sign_eq_zero_iff] at hs
      exact hp hs
  · intro ψ hψ
    by_cases hp : ψ p = 0
    · exact Or.inl (by rw [hp, sign_zero])
    · exact Or.inr (hsign ψ hψ hp).symm
  · rw [vadd_vsub]
    exact W.smul_mem ε v.property

/-- A family fixing `p` has a regular fixed point incident to `p` if every root
through `p` is nonzero on some common fixed linear direction. -/
theorem IsLocallyFiniteReflectionArrangement.exists_regularPoint_fixed
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {I : Type uI} (ρ : I → A ≃ᵃ[ℝ] A) (p : A)
    (hp : ∀ σ, ρ σ p = p)
    (hdir : ∀ ψ ∈ Ψ, ψ p = 0 →
      ∃ v : V, (∀ σ, (ρ σ).linear v = v) ∧ ψ.linear v ≠ 0) :
    ∃ x : A, IsRegular Ψ x ∧ p ∈ facetClosure Ψ x ∧ ∀ σ, ρ σ x = x := by
  let W : Submodule ℝ V :=
    { carrier := {v | ∀ σ, (ρ σ).linear v = v}
      zero_mem' := by intro σ; exact map_zero _
      add_mem' := by
        intro v w hv hw σ
        rw [map_add, hv σ, hw σ]
      smul_mem' := by
        intro r v hv σ
        rw [map_smul, hv σ] }
  obtain ⟨x, hx, hpx, hxW⟩ := hΨ.exists_regularPoint_in_subspace p W (by
    intro ψ hψ hψp
    obtain ⟨v, hv, hψv⟩ := hdir ψ hψ hψp
    exact ⟨⟨v, hv⟩, hψv⟩)
  refine ⟨x, hx, hpx, fun σ => ?_⟩
  calc
    ρ σ x = ρ σ ((x -ᵥ p) +ᵥ p) := by rw [vsub_vadd]
    _ = (ρ σ).linear (x -ᵥ p) +ᵥ ρ σ p := (ρ σ).map_vadd _ _
    _ = x := by rw [hxW σ, hp σ, vsub_vadd]

/-- A chosen regular common fixed point, retaining incidence with the initial
fixed point. The root nonvanishing condition is an explicit input. -/
def invariantRegularPoint
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {I : Type uI} (ρ : I → A ≃ᵃ[ℝ] A) (p : A)
    (hp : ∀ σ, ρ σ p = p)
    (hdir : ∀ ψ ∈ Ψ, ψ p = 0 →
      ∃ v : V, (∀ σ, (ρ σ).linear v = v) ∧ ψ.linear v ≠ 0) :
    {x : A // IsRegular Ψ x ∧ p ∈ facetClosure Ψ x ∧ ∀ σ, ρ σ x = x} :=
  ⟨(hΨ.exists_regularPoint_fixed ρ p hp hdir).choose,
    (hΨ.exists_regularPoint_fixed ρ p hp hdir).choose_spec⟩

/-- When the family also preserves roots, the chosen point's whole ordinary
facet is invariant. -/
theorem image_facet_invariantRegularPoint
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {I : Type uI} (ρ : I → A ≃ᵃ[ℝ] A) (p : A)
    (hp : ∀ σ, ρ σ p = p)
    (hdir : ∀ ψ ∈ Ψ, ψ p = 0 →
      ∃ v : V, (∀ σ, (ρ σ).linear v = v) ∧ ψ.linear v ≠ 0)
    (hρ : ∀ σ, ρ σ ∈ rootStabilizer Ψ) (σ : I) :
    ρ σ '' facet Ψ (invariantRegularPoint hΨ ρ p hp hdir).val =
      facet Ψ (invariantRegularPoint hΨ ρ p hp hdir).val := by
  rw [image_facet (hρ σ), (invariantRegularPoint hΨ ρ p hp hdir).property.2.2 σ]

end Langlands.Geometry.Building.AffineRootSystem
