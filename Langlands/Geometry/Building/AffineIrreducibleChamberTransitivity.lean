import Langlands.Geometry.Building.AffineIrreducibleChamberVertices
import Langlands.Geometry.Building.AffineTransitiveRootLengths
import Langlands.GroupScheme.SimplyConnected.AffineCartanTransitiveShape

/-!
# Chamber transitivity from a group with at most one fixed point

Let `Γ` be a group of root-preserving affine automorphisms of a nonempty irreducible affine root
system `Ψ` that stabilizes the chamber of a regular point `c` and has at most one fixed point in
the closed chamber. Then any simple affine root of the chamber is carried to any other by an
element of the root stabilizer (`HasTransitiveSimpleRoots`), and the chamber Cartan matrix is
vertex transitive (`AffineCartan.IsVertexTransitive`). These are the two chamber-transitivity
premises in the proof of KP Theorem 10.3.1.

The fixed-point hypothesis holds as soon as the linear parts of `Γ` have no common nonzero fixed
vector, since two common fixed points differ by such a vector. The results are also stated for
the image of a group homomorphism `ρ : M →* (A ≃ᵃ[ℝ] A)`, the form in which a Galois group acts
on an apartment.
-/

noncomputable section

universe uV uA uM

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- If no nonzero vector is fixed by the linear parts of every element of `Γ`, then the common
fixed points of `Γ` form a subsingleton: two of them differ by such a vector. -/
theorem fixedPoints_subsingleton_of_linear {Γ : Set (A ≃ᵃ[ℝ] A)}
    (hlin : ∀ v : V, (∀ e ∈ Γ, e.linear v = v) → v = 0) :
    {y : A | ∀ e ∈ Γ, e y = y}.Subsingleton := by
  intro x hx y hy
  have h : y -ᵥ x = 0 := hlin _ fun e he => by
    have h1 := (e : A →ᵃ[ℝ] A).linearMap_vsub y x
    rw [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_toAffineMap, hx e he, hy e he] at h1
    exact h1
  exact (vsub_eq_zero_iff_eq.mp h).symm

namespace IsAffineRootSystemWithRankZero

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ) {c : A}

include hΨ

/-- For a nonempty irreducible affine root system and a group `Γ` of root-preserving affine
automorphisms stabilizing the chamber of `c` with at most one fixed point in its closure, any
simple affine root of the chamber is the pullback of any other along an element of the root
stabilizer. -/
theorem hasTransitiveSimpleRoots_of_subsingleton
    (hirr : IsIrreducibleRoots Ψ) (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (Γ : Subgroup (A ≃ᵃ[ℝ] A)) (hΓ : Γ ≤ rootStabilizer Ψ)
    (hΓC : ∀ e ∈ Γ, e '' facet Ψ c = facet Ψ c)
    (hfix : {y | y ∈ facetClosure Ψ c ∧ ∀ e ∈ Γ, e y = y}.Subsingleton) :
    HasTransitiveSimpleRoots Ψ (facet Ψ c) := by
  intro ψ hψ η hη
  obtain ⟨e, he, hηe⟩ :=
    hΨ.exists_mem_eq_comp_symm_of_subsingleton_of_isIrreducibleRoots hirr hc hne Γ hΓ hΓC
      hfix hψ hη
  refine ⟨e.symm, ?_, hηe⟩
  rw [← AffineEquiv.inv_def]
  exact inv_mem (hΓ he)

/-- Under the hypotheses of `hasTransitiveSimpleRoots_of_subsingleton`, the entry-preserving
permutations of the chamber Cartan matrix act transitively on the simple affine roots. -/
theorem isVertexTransitive_chamberCartanMatrix_of_subsingleton
    [Fintype (simpleAffineRoots Ψ (facet Ψ c))]
    (hirr : IsIrreducibleRoots Ψ) (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (Γ : Subgroup (A ≃ᵃ[ℝ] A)) (hΓ : Γ ≤ rootStabilizer Ψ)
    (hΓC : ∀ e ∈ Γ, e '' facet Ψ c = facet Ψ c)
    (hfix : {y | y ∈ facetClosure Ψ c ∧ ∀ e ∈ Γ, e y = y}.Subsingleton) :
    Langlands.GroupScheme.AffineCartan.IsVertexTransitive
      (chamberCartanMatrix Ψ (facet Ψ c)) :=
  fun ψ η =>
    hΨ.exists_perm_chamberCartanMatrix_apply_eq_of_subsingleton hirr hc hne Γ hΓ hΓC hfix ψ η

/-- Both chamber-transitivity conclusions for the image of a group homomorphism
`ρ : M →* (A ≃ᵃ[ℝ] A)` by root-preserving automorphisms stabilizing the chamber of `c`, provided
the linear parts of all `ρ m` have no common nonzero fixed vector. -/
theorem chamberTransitivity_of_hom_of_linear
    [Fintype (simpleAffineRoots Ψ (facet Ψ c))]
    (hirr : IsIrreducibleRoots Ψ) (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    {M : Type uM} [Group M] (ρ : M →* (A ≃ᵃ[ℝ] A)) (hρ : ∀ m, ρ m ∈ rootStabilizer Ψ)
    (hρC : ∀ m, ρ m '' facet Ψ c = facet Ψ c)
    (hlin : ∀ v : V, (∀ m, (ρ m).linear v = v) → v = 0) :
    HasTransitiveSimpleRoots Ψ (facet Ψ c) ∧
      Langlands.GroupScheme.AffineCartan.IsVertexTransitive
        (chamberCartanMatrix Ψ (facet Ψ c)) := by
  have hΓ : ρ.range ≤ rootStabilizer Ψ := by
    rintro _ ⟨m, rfl⟩
    exact hρ m
  have hΓC : ∀ e ∈ ρ.range, e '' facet Ψ c = facet Ψ c := by
    rintro _ ⟨m, rfl⟩
    exact hρC m
  have hfix : {y | y ∈ facetClosure Ψ c ∧ ∀ e ∈ ρ.range, e y = y}.Subsingleton := by
    refine (fixedPoints_subsingleton_of_linear (Γ := (ρ.range : Set (A ≃ᵃ[ℝ] A)))
      fun v hv => hlin v fun m => hv (ρ m) ⟨m, rfl⟩).anti ?_
    intro y hy
    exact hy.2
  exact ⟨hΨ.hasTransitiveSimpleRoots_of_subsingleton hirr hc hne ρ.range hΓ hΓC hfix,
    hΨ.isVertexTransitive_chamberCartanMatrix_of_subsingleton hirr hc hne ρ.range hΓ hΓC hfix⟩

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
