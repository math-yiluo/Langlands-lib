import Langlands.Representation.Unitary.AdmissibleSemisimplicityStatement

/-!
# The orthogonal of an invariant subspace (Renard IV.2.2, Proposition)

For an admissible representation with an invariant positive definite Hermitian form, the
orthogonal `V₁^⊥` of an invariant subspace `V₁` is invariant and `V = V₁ ⊕ V₁^⊥`.
Compact open subgroups must be cofinal among open subgroups, as in
`AdmissibleUnitarySemisimplicityStatement`.
-/

namespace Langlands

universe uG uV

/-- Renard IV.2.2, Proposition: let `ρ` be an admissible representation of a topological
group in which compact open subgroups are cofinal among open subgroups, with an invariant
positive definite Hermitian form `b`. For every `G`-stable subspace `V₁`, the orthogonal
`V₁^⊥ = {v | ∀ v₁ ∈ V₁, b(v, v₁) = 0}` is a `G`-stable subspace and `V = V₁ ⊕ V₁^⊥`. -/
def AdmissibleUnitaryOrthogonalComplementStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V), IsAdmissible ρ →
      ∀ (b : InvariantPositiveForm ρ) (V₁ : Submodule ℂ V),
        (∀ (g : G), ∀ v ∈ V₁, ρ g v ∈ V₁) →
        ∃ W : Submodule ℂ V,
          (W : Set V) = {v | ∀ v₁ ∈ V₁, b.inner v v₁ = 0} ∧
            (∀ (g : G), ∀ v ∈ W, ρ g v ∈ W) ∧ IsCompl V₁ W

end Langlands
