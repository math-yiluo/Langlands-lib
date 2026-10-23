# Finite-extension descent along a directed union: proof

Author: Worker 29.

The theorem `Langlands.FieldTheory.finiteExtensionDirectedUnionDescent.{u,v}`
proves exactly the published proposition
`Langlands.FieldTheory.FiniteExtensionDirectedUnionDescent.{u,v}`. It has no
additional hypotheses. The fields have universe `u`; the directed family's
index type has the independent universe `v`.

## One stage and one descended field

Choose Mathlib's finite basis `b` of `M` over `L`. Form a finite set of elements
of `M` containing `1`, the prescribed set `s`, every product of two basis
vectors, and every image of a basis vector under every `L`-automorphism of
`M`. The automorphism group is finite for every finite extension, including
extensions that are not Galois. Collect all coordinates of these elements in
`b`, and also all nonzero coefficients of the minimal polynomial over `L` of
each basis vector. No separability or Galois hypothesis is used in this
selection.

The private lemma `finite_subset_stage` uses induction on a finite set,
covering, and directedness to find a stage containing this entire coefficient
set and the prescribed initial stage. This does not require an order on the
index type. All later clauses use this same chosen index `i`.

Put `F = A i`. The private lemma `basis_span_field` constructs the `F`-span
of the original basis inside `M`. Mathlib's `Basis.mem_span_iff_repr_mem`
identifies this span with the elements whose coordinates belong to `F`.
The chosen coordinates of `1` and the products show that the span is a
unital subalgebra; multiplication closure is proved by two span inductions.
It is finite dimensional. Hence it is algebraic, and
`Algebra.IsAlgebraic.toIntermediateField` supplies inverse closure, producing
an actual intermediate field `B` with the same underlying span.

`Basis.restrictScalars` gives an `F`-basis `c` of `B` whose images in `M` are
exactly the vectors of `b`. Their equal finite index types give the degree
equality. The original `L`-linear independence and
`IntermediateField.LinearDisjoint.of_basis_left` give the required linear
disjointness. Expanding arbitrary elements in `b` proves
`IntermediateField.adjoin L (B : Set M) = top`. The coordinate criterion
puts every element of `s` in `B`.

Throughout, the proof installs `Algebra.ofSubsemiring (A i)` on `L` and
`M` and `IsScalarTower.of_algebraMap_eq' rfl`, exactly as in the statement.
The map to `M` is the stage inclusion followed by the given `algebraMap L M`;
`B` has its canonical intermediate-field scalar structure and subtype map.

## Separability in arbitrary characteristic

The proof uses polynomial coefficients instead of Serre's purely inseparable
base-extension argument. The private lemma `separable_of_minpoly_coeffs`
uses `Polynomial.mem_map_range` to obtain an `F`-polynomial whose image in
`L[X]` is the original minimal polynomial of a basis vector. When `M/L` is
separable, `Polynomial.separable_map` implies that this descended polynomial
is separable. Compatibility of evaluation with the literal scalar maps shows
that the basis vector is a root. Its minimal polynomial over `F` divides
this separable polynomial, so the vector is separable over `F`.

The private lemma `basis_separable` expands every element of `B` in `c` and
places it in `separableClosure F M`. The equivalence
`le_separableClosure_iff` then proves `Algebra.IsSeparable F B`. This uses
no restriction on the characteristic and no enlargement of the chosen stage.

## Galois refinement

When `M/L` is Galois, the coordinates already selected ensure that every
`L`-automorphism sends every basis vector into `B`. The private lemma
`basis_galois` expands arbitrary elements of `B` to show that restriction
defines an `F`-algebra endomorphism of `B`. Distinct automorphisms have distinct
restrictions: equality on `B` implies equality on `b`, hence equality on `M`.

This injection gives at least `[M:L] = [B:F]` endomorphisms of `B`; Mathlib's
`AlgHom.card_le` gives the reverse bound. The equivalence
`algEquivEquivAlgHom F B` identifies these endomorphisms with automorphisms
of the finite extension. `IsGalois.of_card_aut_eq_finrank` proves Galoisness.
Thus both conditional refinements hold for the same `i,B` selected before
either hypothesis was introduced.

## Provenance and dependencies

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, GTM 67, Springer (1979), Chapter V, section 4, Lemma 6 and its proof,
printed page 89 (PDF page 96). Registered source: `serre-1979-local-fields`;
file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`; SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The original page and the following page were read. No project errata note
for this source was found. The stage and finite-set strengthening is explained
in the published statement, authored by Worker 29 with Worker 10's requested
formulation.

The structure-constant construction and automorphism stabilization follow
Serre's proof strategy. Including coordinates of `1` avoids requiring the
chosen basis itself to contain `1`. The polynomial-coefficient separability
argument and the explicit finite set combining all constraints are internal
derivations. No other worker's proof draft was used.

The only project dependency is the unchanged published statement module.
Additional Mathlib imports are `LinearAlgebra.Basis.Submodule`,
`Algebra.Polynomial.Eval.Subring`, and `FieldTheory.SeparableClosure`, in the
pinned Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`
environment. The helpers belong to this single proof and are private.

This result does not assert eventual uniqueness, simultaneous descent of a
finite tower, a local-field identification, or norm surjectivity. No valuation,
common finite ground field, or local-field structure occurs in its hypotheses.
