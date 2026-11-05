# Perfect-field comparison of pseudo-reductivity and reductivity

`perfectFieldPseudoReductive` proves the exact published proposition
`PerfectFieldPseudoReductiveStatement` in every universe `u`: for every
perfect field `k` and actual group scheme `G` over `Spec k`,
`IsPseudoReductive G ↔ IsConnectedReductive G`.

For the forward implication, perfectness makes the algebraic extension
`AlgebraicClosure k / k` separable, and an algebraic closure is normal.
Together these give its Galois instance in arbitrary characteristic. Apply
`IsPseudoReductive.baseChange_galois` to this extension. The resulting
ground-field trivial radical over the algebraic closure is precisely the
geometric trivial-radical condition in `IsConnectedReductive`. Smoothness,
affineness and connectedness are copied from the original pseudo-reductive
group. The reverse implication reuses the published theorem
`IsConnectedReductive.isPseudoReductive`, which holds over every field.

The Galois ascent theorem constructs and descends the represented radical
through its full tensor-coordinate defining ideal and the actual scheme
ideal sheaf. Thus the proof supplies every radical comparison and descent
condition internally. It retains the published intrinsic ground-field and
geometric predicates, arbitrary characteristic, arbitrary universe, and all
relative test schemes, including nonreduced tests. There is no supplied
radical, affine presentation, classification or splitness premise.

The target's source and mathematical correspondence are recorded in
`PerfectFieldStatement.md` (Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition, Definition 1.1.1, printed p. 3 and the opening paragraph
of p. 4). This Markdown describes the implemented proof through the imported
Galois descent constructions. Worker 1359 authored the final assembly and
scheme ideal-descent adapters; Worker 1370 authored the tensor-coordinate
and Galois ideal-descent proofs used by the assembly.
