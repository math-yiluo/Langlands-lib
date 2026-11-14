import Langlands.Geometry.Building.AffineChamberVertexSimpleRoots
import Langlands.Geometry.Building.AffineIrreducibleSimpleRoots

/-!
# Vertices of a chamber of an irreducible affine root system

For a nonempty irreducible affine root system (KP Definition 1.3.13), the simple affine roots of
a chamber are linearly independent (KP Proposition 1.3.22(5)), so the results on vertices and
simple affine roots, which take this linear independence as a hypothesis, apply without it:
the vertices of the closure of a chamber correspond to its simple affine roots (KP Proposition
1.3.22(6)), naturally for root-preserving affine automorphisms stabilizing the chamber, and a
group of such automorphisms with at most one fixed point in the closed chamber acts transitively
on the simple affine roots and therefore by permutations preserving the chamber Cartan matrix.
-/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

namespace IsAffineRootSystemWithRankZero

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ) {c : A}

include hΨ

/-- KP Proposition 1.3.22(6) for an irreducible affine root system: the points of the closed
chamber that are vertices are exactly the vertices opposite to the walls of its simple affine
roots. -/
theorem mem_facetClosure_and_isVertex_iff_of_isIrreducibleRoots (hirr : IsIrreducibleRoots Ψ)
    (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {x : A} :
    x ∈ facetClosure Ψ c ∧ IsVertex Ψ x ↔
      ∃ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), x = simpleVertex Ψ (facet Ψ c) ψ :=
  hΨ.mem_facetClosure_and_isVertex_iff (hΨ.linearIndependent_simpleAffineRoots hirr hc) hc hne

/-- KP Proposition 1.3.22(6) for an irreducible affine root system: `ψ ↦ simpleVertex Ψ C ψ` is
a bijection from the simple affine roots of the chamber `C` onto the vertices of its closure. -/
def simpleVertexEquivOfIsIrreducibleRoots (hirr : IsIrreducibleRoots Ψ) (hc : IsRegular Ψ c)
    (hne : Ψ.Nonempty) :
    simpleAffineRoots Ψ (facet Ψ c) ≃ {x : A // x ∈ facetClosure Ψ c ∧ IsVertex Ψ x} :=
  hΨ.simpleVertexEquiv (hΨ.linearIndependent_simpleAffineRoots hirr hc) hc hne

@[simp]
theorem coe_simpleVertexEquivOfIsIrreducibleRoots_apply (hirr : IsIrreducibleRoots Ψ)
    (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) (ψ : simpleAffineRoots Ψ (facet Ψ c)) :
    (hΨ.simpleVertexEquivOfIsIrreducibleRoots hirr hc hne ψ : A) =
      simpleVertex Ψ (facet Ψ c) ψ :=
  rfl

/-- For an irreducible affine root system, a root-preserving automorphism stabilizing the
chamber maps the vertex opposite to `ψ` to the vertex opposite to `ψ ∘ e⁻¹`. -/
theorem apply_simpleVertex_of_isIrreducibleRoots (hirr : IsIrreducibleRoots Ψ)
    (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ)
    (hC : e '' facet Ψ c = facet Ψ c) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    e (simpleVertex Ψ (facet Ψ c) ψ) =
      simpleVertex Ψ (facet Ψ c) (ψ.comp (e.symm : A →ᵃ[ℝ] A)) :=
  hΨ.apply_simpleVertex (hΨ.linearIndependent_simpleAffineRoots hirr hc) hc hne he hC hψ

/-- For an irreducible affine root system, a group of root-preserving affine automorphisms
stabilizing a chamber with at most one fixed point in the closure of the chamber acts
transitively on the simple affine roots of the chamber. -/
theorem exists_mem_eq_comp_symm_of_subsingleton_of_isIrreducibleRoots
    (hirr : IsIrreducibleRoots Ψ) (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (Γ : Subgroup (A ≃ᵃ[ℝ] A)) (hΓ : Γ ≤ rootStabilizer Ψ)
    (hΓC : ∀ e ∈ Γ, e '' facet Ψ c = facet Ψ c)
    (hfix : {y | y ∈ facetClosure Ψ c ∧ ∀ e ∈ Γ, e y = y}.Subsingleton)
    {ψ η : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c))
    (hη : η ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    ∃ e ∈ Γ, η = ψ.comp (e.symm : A →ᵃ[ℝ] A) :=
  hΨ.exists_mem_eq_comp_symm_of_subsingleton (hΨ.linearIndependent_simpleAffineRoots hirr hc)
    hc hne Γ hΓ hΓC hfix hψ hη

/-- For an irreducible affine root system and a group `Γ` as in
`exists_mem_eq_comp_symm_of_subsingleton_of_isIrreducibleRoots`, any simple affine root of the
chamber is sent to any other by a permutation of the simple affine roots preserving every entry
of the chamber Cartan matrix. -/
theorem exists_perm_chamberCartanMatrix_apply_eq_of_subsingleton
    (hirr : IsIrreducibleRoots Ψ) (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (Γ : Subgroup (A ≃ᵃ[ℝ] A)) (hΓ : Γ ≤ rootStabilizer Ψ)
    (hΓC : ∀ e ∈ Γ, e '' facet Ψ c = facet Ψ c)
    (hfix : {y | y ∈ facetClosure Ψ c ∧ ∀ e ∈ Γ, e y = y}.Subsingleton)
    (ψ η : simpleAffineRoots Ψ (facet Ψ c)) :
    ∃ σ : Equiv.Perm (simpleAffineRoots Ψ (facet Ψ c)),
      (∀ k l, chamberCartanMatrix Ψ (facet Ψ c) (σ k) (σ l) =
        chamberCartanMatrix Ψ (facet Ψ c) k l) ∧ σ ψ = η :=
  hΨ.exists_perm_chamberCartanMatrix_apply_eq (Γ := (Γ : Set (A ≃ᵃ[ℝ] A)))
    (fun _ he => hΓ he) hΓC
    (fun ψ η => hΨ.exists_mem_eq_comp_symm_of_subsingleton_of_isIrreducibleRoots hirr hc hne
      Γ hΓ hΓC hfix ψ.2 η.2) ψ η

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
