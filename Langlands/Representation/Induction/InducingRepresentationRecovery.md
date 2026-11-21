# Smooth induction reflects admissibility

This helper works with the Library's unnormalized `Induction.smoothInduced P τ`
for a subgroup `P` of a topological group `G` and a representation `τ` of `P`
on an `R`-module, with `R` a commutative ring. The group, coefficient ring,
and carrier universes are independent.

## Fixed vectors and evaluation

`Langlands.Induction.fixedEvaluationAt P τ K x` is the linear map from the
`K`-fixed vectors of the smooth induction to the coefficient vectors fixed
by the subgroup \(P \cap xKx^{-1}\) of `P`. Here `K` is open. The
fixedness of the value at `x` is the Library's `eval_mem_fixedVectors`.

For compact open `K`, `fixedEvaluation_one_surjective` shows that evaluation
at `1` is onto the `(P ∩ K)`-fixed space. For a vector `v` in that space the
proof uses `compactDoubleCosetSection P τ K hK 1 v` from
[`CompactLocalSection`](CompactLocalSection.md). The section equals `τ p v`
at `p * k`, and is zero off `P * K`. Its right-`K` invariance puts it in the
source fixed space and its value at `1` is `v`. This uses the same construction
as the evaluation-surjectivity argument in Casselman, *Introduction to the
theory of admissible representations of p-adic reductive groups*, draft
1 May 1995 (`casselman-1995-admissible-representations`), proof of Theorem
2.4.1(b), p. 27. The Lean result fixes `K` and concerns its fixed space.

## Admissibility and inflation

`Langlands.Induction.isAdmissible_of_smoothInduced` assumes `G` is
nonarchimedean and weakly locally compact, `R` is Noetherian, `τ` is smooth,
and `smoothInduced P τ` is admissible. For an open subgroup `H` of `P`, choose
an open identity neighborhood in `G` with preimage `H` in `P`. Choose a
compact open `K` inside that neighborhood using `compactOpenSubgroupBasis`.
Then `P ∩ K ≤ H`. Admissibility gives a finite `R`-module of `K`-fixed induced
vectors. The surjection just proved gives finiteness of the `(P ∩ K)`-fixed
coefficient module. The `H`-fixed vectors inject into the latter, so they are
finite by Noetherianity. This proves admissibility of `τ`; there is no
closedness or quotient compactness requirement on `P` in this implication.

`Langlands.Induction.isIrreducible_of_comp_surjective` is a separate algebraic
helper over a field. It reflects irreducibility along a surjective group
homomorphism `m`. The same invariant submodule for a representation of the
target is invariant for the pullback; conversely, lift each target element
through `m` to check invariance. Lean packages these two operations as an
order isomorphism of subrepresentation lattices and transports simplicity of
the lattice. There is no topological hypothesis on this lemma.

These are derived helpers for the proper-parabolic non-induction argument.
They prove no converse for admissibility of arbitrary smooth inductions.
