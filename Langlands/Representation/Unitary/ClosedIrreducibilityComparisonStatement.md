# Closed and algebraic irreducibility for an admissible positive form

Authors: Worker 452 and Worker 581.

`Langlands.AdmissibleClosedIrreducibilityComparisonStatement.{uG,uV,uH}`
is an internal proposition definition for the comparison between a normed
realization and an algebraic smooth representation. It states a prerequisite;
it contains no proof.

For a topological group `G : Type uG`, with `Group G`, `TopologicalSpace G`
and `IsTopologicalGroup G`, compact open subgroups must be cofinal among open
subgroups:

```lean
∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
  IsCompact (L : Set G) ∧ L ≤ K
```

The carrier `V : Type uV` has `AddCommGroup V` and `Module ℂ V`, with
`ρ : Representation ℂ G V`. It has no assumed norm or topology.
`Langlands.IsAdmissible ρ` requires smoothness (each vector is fixed by an
open subgroup) and finite dimensionality of the fixed space for **every open
subgroup**. The chosen
`b : Langlands.InvariantPositiveForm ρ` is an actual positive definite
invariant Hermitian form.

The target then quantifies over `H : Type uH` with `NormedAddCommGroup H`
and `InnerProductSpace ℂ H`,
an action `π : G →* (H →L[ℂ] H)`, and a complex-linear map `j : V →ₗ[ℂ] H`.
It requires that `j` have dense range, intertwine the given actions, and satisfy

```lean
inner ℂ (j v) (j w) = b.inner v w
```

for every `v,w`. Positive definiteness implies injectivity of `j`; this is not
an additional hypothesis. Each operator `π g` is continuous because it is a
continuous linear map. Neither completeness of `H` nor joint continuity of
the action is required by this comparison. All three universes are independent.

The last hypothesis is the existing
`Langlands.Archimedean.IsTopologicallyIrreducible π`: `H` is nonzero and each
closed, invariant complex submodule of `H` is either zero or the whole space.
Although its namespace is `Archimedean`, that definition has no Lie-group,
manifold, differentiability or field-locality hypotheses. It is reused with its
actual generic meaning. The conclusion is the existing algebraic predicate
`Representation.IsIrreducible ρ`, which rules out every nontrivial invariant
algebraic submodule and requires a nonzero carrier.

This statement is derived internal infrastructure rather than a transcription
of a literature theorem. Its intended justification uses the published
`Langlands.InvariantPositiveForm.toSmoothDual_surjective` from
[`Langlands.Representation.Unitary.HermitianDual`](HermitianDual.md), as in
[`Langlands.admissibleUnitarySemisimplicity`](AdmissibleSemisimplicityProof.md).
For an invariant algebraic subspace `S`, admissibility passes to `S` by
[`Langlands.isAdmissible_of_injective`](../Smooth/Admissibility/EmbeddingProof.md).
Restricting the form and using smooth-dual surjectivity decomposes each vector
as a vector of `S` plus a vector orthogonal to `S`. Form preservation and
continuity of the inner product then imply that a dense image of `S` forces
`S = V`. The closure of `j(S)` is invariant under the continuous operators
`π g`; closed irreducibility therefore leaves only `S = 0` or `S = V`.
Density and the nonzero ambient carrier ensure `V` is nonzero. This paragraph
explains the provenance and a proposed proof, not an implemented proof.

This proposition definition supplies no proof, completion construction,
smooth-vector recovery, induction model, Haar comparison, or induction
irreducibility theorem. Applying this comparison to normalized block induction
requires the actual form, realization, and closed-irreducibility hypothesis to
be established separately for that induced representation.
