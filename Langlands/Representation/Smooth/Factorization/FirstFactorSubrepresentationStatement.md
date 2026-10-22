# An admissible irreducible first-factor subrepresentation

This pair states one internal prerequisite of the existence clause of Flath's
two-factor theorem. Its entry declaration is the proposition definition
`Langlands.AdmissibleProductFirstFactorSubrepresentationStatement.{uG₁,uG₂,uV}`
in module
`Langlands.Representation.Smooth.Factorization.FirstFactorSubrepresentationStatement`.
It is a `def` whose value is a `Prop`. The pair does not assume or prove that
the proposition is true.

## The proposition

Let `G₁` and `G₂` be topological groups that are Hausdorff, locally compact
and totally disconnected. Let `V` be a complex vector space and `ρ` a
representation of `G₁ × G₂` on `V`. Suppose `ρ` is admissible and
irreducible. Then there exist

- a subrepresentation `S` of the restriction `ρ.comp (MonoidHom.inl G₁ G₂)`,
  that is, of `g₁ ↦ ρ (g₁, 1)`, and
- an open subgroup `K₂` of `G₂` whose underlying set is compact,

such that

1. `ρ (1, k₂) v = v` for every `k₂ ∈ K₂` and every `v ∈ S`;
2. the representation `S.toRepresentation` of `G₁` on `S` is admissible;
3. `S.toRepresentation` is irreducible.

In Lean the conclusion reads

```lean
∃ (S : Subrepresentation (ρ.comp (MonoidHom.inl G₁ G₂)))
  (K₂ : OpenSubgroup G₂),
  IsCompact (K₂ : Set G₂) ∧
  (∀ k₂ ∈ K₂, ∀ v ∈ S.toSubmodule, ρ (1, k₂) v = v) ∧
  IsAdmissible S.toRepresentation ∧ S.toRepresentation.IsIrreducible
```

The hypotheses are `IsAdmissible ρ` and `ρ.IsIrreducible`.

## The objects used

- `Subrepresentation` is Mathlib's. Its carrier `S.toSubmodule` is an actual
  complex subspace of `V`, so `S` lives in the universe `uV` of `V`. The
  action of `S.toRepresentation g₁` is `ρ (g₁, 1)` on vectors of `S`.
  This holds definitionally.
- Condition 1 says exactly that `S.toSubmodule` is contained in the fixed
  space `fixedVectors (ρ.comp (MonoidHom.inr G₁ G₂)) K₂.toSubgroup`. This is
  the space of vectors fixed by `(1, k₂)` for all `k₂ ∈ K₂`. The Lean states
  it as explicit action equations.
- `K₂` is a genuine `OpenSubgroup G₂`, and its compactness is the topological
  predicate `IsCompact` on its underlying set.
- `Langlands.IsAdmissible` is the published definition in
  `Langlands.Representation.Smooth.Definitions`. It asks that every vector is
  fixed by some open subgroup, and that the fixed space of every open subgroup
  is a finitely generated module. Over `ℂ` this means finite-dimensional.
  This is the all-open-subgroups convention. It is used both for `ρ` and for
  `S.toRepresentation`.
- `Representation.IsIrreducible` is Mathlib's. It requires the representation
  to be nonzero, so the conclusion forces `S ≠ 0`.

All groups, instances, the space and the representation are quantified
inside the proposition. The universes `uG₁` and `uG₂` of the groups and `uV`
of the space vary independently. The statement has no smallness hypothesis
and no supplied factorization. It does not assume that `V` is
finite-dimensional, and it assumes no unitarity, reductivity or second
countability. The topological-group hypotheses match those of
`Langlands.AdmissibleProductFactorizationStatement` in
`Langlands.Representation.Smooth.Factorization.TwoFactorStatement`.

## Provenance

Source: D. Flath, *Decomposition of representations into tensor products*,
in *Automorphic Forms, Representations and L-functions*, Proceedings of
Symposia in Pure Mathematics 33, Part 1 (1979), pp.179–183.

- Literature ID: `flath-1979-tensor-products`.
- Retained original: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
  SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
- Locator: Theorem 1, clause (1.2), printed p.179, and its proof, printed
  p.180 (one-based PDF pages 175–176).

Flath does not state this proposition as a separate result, so it is an
internal, derived intermediary. Clause (1.2) gives `W ≅ W₁ ⊗ W₂` with
admissible irreducible factors `Wᵢ`. The proof ends by noting that the
restriction of `W` to `Gᵢ` is `Wᵢ`-isotypic. In such a factorization, choose
a compact open `K₂` with `W₂^{K₂} ≠ 0` and a nonzero `w₂ ∈ W₂^{K₂}`. Then
`W₁ ⊗ w₂` is a `G₁`-subrepresentation isomorphic to `W₁` and fixed by
`1 × K₂`. The proposition asserts the existence of such a constituent
directly, as a subspace of the given space and without a factorization.
That is the form in which the constituent serves as a first step toward the
factorization. Flath's own proof instead uses the finite-dimensional Hecke
corners `H(G₁,K₁) ⊗ H(G₂,K₂)` acting on `W^{K₁×K₂}` and an inductive system
over shrinking compact open subgroups.

The source uses compact open subgroups. The admissibility in this statement
is the published all-open-subgroups convention, as in the target
`TwoFactorStatement` pair. For the groups in question the two conventions
agree. Every open subgroup contains a compact open subgroup (van Dantzig),
and the fixed space of the larger subgroup lies inside the fixed space of
the smaller one.

## Intended proof route

This section describes a plan only. This pair contains no proof.

1. Pick a nonzero `x ∈ V`, an open subgroup of `G₁ × G₂` fixing `x`, a
   compact open `K₁ ≤ G₁` inside its first-factor pullback, and a compact
   open `K₂ ≤ G₂` inside its second-factor pullback. Then
   `M = V^{K₁} ∩ V^{K₂}` lies in `V^{K₁×K₂}`, so it is finite-dimensional,
   and it contains `x`.
2. Averaging over `K₁`, together with the irreducibility of `ρ`, shows that
   every nonzero `G₁`-subrepresentation of `V` meets `V^{K₁}` nontrivially.
   The averaging operator commutes with the `G₂`-action.
3. Choose a nonzero `y ∈ M` that minimizes the dimension of
   `span(G₁·y) ∩ M`. Then every nonzero `u ∈ span(G₁·y)` regenerates `y`. So
   `S = span(G₁·y)` is irreducible. It is fixed by `1 × K₂` because
   `V^{K₂}` is `G₁`-stable.
4. For every open `L ≤ G₁`, `S^L` embeds in `V^{L×K₂}`. That space is
   finite-dimensional by the admissibility of `ρ`, so `S` is admissible.

The published module
`Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`
already contains closely related internal lemmas in namespace
`Langlands.TwoFactorExistence`: `exists_cyclic`, `isIrreducible_spanOrbit`,
`secondFixed` and `isAdmissible_of_le_secondFixed`. There, the `K₂`
produced by `exists_cyclic` is only open. A proof of this proposition must
still supply a compact open subgroup inside it, for example from van
Dantzig's theorem for `G₂`. The proof belongs to a separate task against
this exact declaration.

## Dependencies

The only project import is the published
`Langlands.Representation.Smooth.Definitions`, which is unchanged: Lean
SHA256 `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`,
Markdown SHA256
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
Mathlib supplies `Representation`, `Subrepresentation`,
`Representation.IsIrreducible`, `OpenSubgroup`, `IsCompact`,
`MonoidHom.inl` and the topological-group classes. The environment is
Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
environment artifact `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

Worker 296 wrote this statement pair. Worker 288 published the task and
chose the declaration name. Compilation and inspection show only that the
proposition is well formed. Independent semantic review and publication
are still required.
