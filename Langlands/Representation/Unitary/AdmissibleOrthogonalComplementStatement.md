# The orthogonal of an invariant subspace (Renard IV.2.2, Proposition): statement

Module `Langlands.Representation.Unitary.AdmissibleOrthogonalComplementStatement`.
Namespace `Langlands`. Universe parameters `uG` (the group) and `uV` (the carrier).
The module contains one **statement**, the `Prop`-valued definition
`AdmissibleUnitaryOrthogonalComplementStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published
[AdmissibleSemisimplicityStatement](AdmissibleSemisimplicityStatement.md) states that an
admissible unitarizable representation is semisimple: every invariant subspace has *some*
invariant complement. Its proof ([AdmissibleSemisimplicityProof](AdmissibleSemisimplicityProof.md))
builds the orthogonal complement, but the theorem's type asserts only existence. Renard's
Proposition asserts more: the complement is the orthogonal `V₁^⊥` for the given form. This
unit states that assertion.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read IV.2.2, printed pp.97–98 / PDF pp.103–104:

> Proposition. Soit `(π, V)` une représentation lisse unitaire admissible du groupe t.d. `G`
> pour le produit hermitien `⟨. , .⟩_V`. Si `V₁` est un sous-espace `G`-stable de `V` alors
> `V₁^⊥ := { v ∈ V | ∀ v₁ ∈ V₁, ⟨v, v₁⟩_V = 0 }` est aussi un sous-espace `G`-stable de `V`
> et `V = V₁ ⊕ V₁^⊥`.

A unitary representation (IV.2.2, Definition) is a smooth representation with a
`G`-invariant positive definite hermitian form.

## Published objects used

- `IsAdmissible ρ` (module `Langlands.Representation.Smooth.Definitions`): `ρ` is smooth
  and its fixed spaces under open subgroups are finite-dimensional.
- `InvariantPositiveForm ρ` (module `Langlands.Representation.Unitary.Basic`): a positive
  definite hermitian form (Mathlib's `InnerProductSpace.Core ℂ V`, conjugate-linear in the
  first variable) preserved by every `ρ g`. `b.inner v w` is its value. No norm, topology or
  completion on `V` is assumed.
- Mathlib's `Submodule ℂ V` and `IsCompl`: for submodules, `IsCompl V₁ W` means
  `V₁ ⊓ W = ⊥` and `V₁ ⊔ W = ⊤`, that is, `V = V₁ ⊕ W` as vector spaces.

## The statement

Let `G` be a topological group in which every open subgroup contains a compact open
subgroup. Let `ρ` be an admissible complex representation of `G` on a vector space `V`, and
let `b` be an invariant positive definite hermitian form. For every subspace `V₁` with
`ρ g v ∈ V₁` for all `g ∈ G` and `v ∈ V₁`, there is a subspace `W` such that

1. its underlying set is `{v | ∀ v₁ ∈ V₁, b(v, v₁) = 0}`, which is Renard's `V₁^⊥`;
2. `W` is `G`-stable;
3. `V = V₁ ⊕ W`.

## Formalization choices

- **The orthogonal as a subspace.** Clause 1 names `V₁^⊥` by its underlying set, and the
  existential packages it as a subspace. That the set is a subspace is immediate, so the
  content is clauses 2 and 3.
- **The group.** Renard's `G` is a t.d. group. Like the published
  `AdmissibleUnitarySemisimplicityStatement`, the statement assumes only that compact open
  subgroups are cofinal among open subgroups. Renard's definition of a t.d. group (II.1.1)
  asks that the identity have a basis of neighbourhoods consisting of compact open
  subgroups, and every open subgroup is such a neighbourhood. So the statement covers
  Renard's setting and is at least as general.
- **The form.** Renard's "représentation lisse unitaire ... pour le produit hermitien
  `⟨. , .⟩_V`" fixes the form. The statement quantifies over all invariant positive forms
  `b` and asserts the conclusion for each. The orthogonality condition `b(v, v₁) = 0` is
  equivalent to `b(v₁, v) = 0` because `b` is hermitian.
- **Admissibility includes smoothness**, as in the published predicate.

## Why the statement is true

Invariance of `V₁^⊥`: if `v ∈ V₁^⊥` and `g ∈ G`, then
`b(ρ g v, v₁) = b(v, ρ g⁻¹ v₁) = 0` for `v₁ ∈ V₁`, since `ρ g⁻¹ v₁ ∈ V₁`.
`V₁ ∩ V₁^⊥ = 0` by positive definiteness. For `V = V₁ + V₁^⊥`, Renard takes `v ∈ V^K` for a
compact open `K` and projects orthogonally inside the finite-dimensional `V^K`. The
published proof of `AdmissibleUnitarySemisimplicityStatement` gives the same decomposition
through the smooth-dual identification of the admissible subrepresentation `V₁`: the
functional `s ↦ b(v, s)` on `V₁` is represented by some `s₀ ∈ V₁`, and `v − s₀ ∈ V₁^⊥`.

## Remaining obligations

The proof is a separate obligation. The published proof of
`AdmissibleUnitarySemisimplicityStatement` constructs exactly this complement and can be
reused.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Unitary.AdmissibleSemisimplicityStatement` | `IsAdmissible`, `InvariantPositiveForm` (through its imports) and the related semisimplicity statement |
