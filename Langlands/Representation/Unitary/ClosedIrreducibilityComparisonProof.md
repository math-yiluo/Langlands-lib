# Closed irreducibility implies algebraic irreducibility

Authors: Worker 203.

`Langlands.admissibleClosedIrreducibilityComparison` proves the complete
proposition
[`Langlands.AdmissibleClosedIrreducibilityComparisonStatement`](ClosedIrreducibilityComparisonStatement.md).
Its type is exactly
`Langlands.AdmissibleClosedIrreducibilityComparisonStatement.{uG,uV,uH}`,
with independent universes for the group, the algebraic carrier and the
normed carrier, and no premises beyond those of the statement. The proof uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Helper lemma

`Langlands.InvariantPositiveForm.exists_sub_inner_eq_zero` is a helper in this
module. Let `G` have compact open subgroups cofinal among its open subgroups,
let `ρ` be admissible with `b : InvariantPositiveForm ρ`, and let `S` be a
subrepresentation. For every vector `v` it gives `s` in `S` with
`b(v - s, t) = 0` for every `t` in `S`.

Its proof is the decomposition step of the published
[`Langlands.admissibleUnitarySemisimplicity`](AdmissibleSemisimplicityProof.md).
The inclusion of `S` is an injective intertwiner, so
[`Langlands.isAdmissible_of_injective`](../Smooth/Admissibility/EmbeddingProof.md)
makes `S` admissible, and `InvariantPositiveForm.comap` restricts `b` to
`S`. Pulling the smooth functional `b(v,-)` back to `S` with
`contragredientMap` gives a smooth functional on `S`. The published
[`InvariantPositiveForm.toSmoothDual_surjective`](HermitianDual.md), applied
to the restricted form, writes it as `b(s,-)` for some `s` in `S`.
Conjugate linearity in the first variable then gives `b(v - s, t) = 0`.

## Proof of the comparison

Write `⟪-,-⟫` for the inner product of `H`. The hypotheses give
`ρ`, `b`, `π` and `j` with dense range, `j(ρ g v) = π g (j v)` and
`⟪j v, j w⟫ = b(v, w)`. Closed irreducibility of `π` supplies that `H` is
nontrivial and that every closed `π`-invariant complex subspace of `H` is
zero or everything.

1. **Injectivity of `j`.** If `j v = 0`, then
   `b(v, v) = ⟪j v, j v⟫ = 0`, so positive definiteness gives `v = 0`.
   Injectivity is derived, not assumed.
2. **`V` is nonzero.** If `V` were a subsingleton, the range of `j` would be
   contained in `{0}`. Its closure, which is all of `H` by density, would be
   contained in the closure of `{0}`, which is `{0}` because `H` is Hausdorff.
   This contradicts nontriviality of `H`. Hence `⊥ ≠ ⊤` among the
   subrepresentations of `ρ`.
3. **The closed invariant subspace attached to `S`.** For a
   subrepresentation `S`, let `C` be the topological closure of the complex
   subspace `j(S)` of `H`. It is closed. For each `g`, equivariance and
   invariance of `S` give `π g (j(S)) ⊆ j(S)`. Since `π g` is a continuous
   linear map, Mathlib's `Submodule.topologicalClosure_map` gives
   `π g (C) ⊆ closure (π g (j(S))) ⊆ C`. Closed irreducibility therefore
   gives `C = 0` or `C = H`.
4. **If `C = 0`, then `S = 0`.** Each `t` in `S` has `j t` in `C`, so
   `j t = 0`, and step 1 gives `t = 0`.
5. **If `C = H`, then `S = V`.** Given `v`, the helper lemma gives `s` in
   `S` with `b(v - s, t) = 0` for all `t` in `S`. Put `x = j(v - s)`. Form
   preservation gives `⟪x, j t⟫ = 0` for every `t` in `S`. So `j(S)` lies in
   the kernel of the continuous functional `innerSL ℂ x = ⟪x, -⟫`. That
   kernel is closed, so it also contains the closure `C = H` of `j(S)`, and
   in particular `x`. Hence
   `b(v - s, v - s) = ⟪x, x⟫ = 0`. Positive definiteness gives `v = s`, which
   lies in `S`.

Steps 2, 4 and 5 are exactly the conditions that make the subrepresentation
lattice of `ρ` a simple order, which is Mathlib's
`Representation.IsIrreducible ρ`.

## Scope and provenance

This is internal derived infrastructure, not a transcription of a literature
theorem. It follows the proof route proposed in the statement's documentation
and its proof task. It uses only each operator `π g` being a continuous linear
map, continuity of the inner product in its second variable, and the Hausdorff
property of the normed space `H`. It does not assume completeness of `H`,
joint continuity of the action, injectivity of `j`, or any norm or topology on
`V`. Admissibility and compact-open cofinality are used only through the
helper lemma's smooth-dual surjectivity.

The module constructs no Hilbert completion, induced positive form,
smooth-vector recovery, normalized induction model, or induction
irreducibility theorem. Applying this comparison to a specific induced
representation requires establishing its form, normed realization and closed
irreducibility separately.
