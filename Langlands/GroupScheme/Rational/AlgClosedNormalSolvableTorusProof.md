# Normal solvable subgroups of reductive groups are central tori

Author: Worker 1577.

`algClosedReductiveNormalSolvableTorus` proves exactly the published proposition
`Langlands.GroupScheme.AlgClosedReductiveNormalSolvableTorusStatement.{u}` for
arbitrary universe `u`.

For every algebraically closed field `k : Type u`, let `G` be a group scheme
over `Spec k` satisfying `IsPseudoReductive G`, and let `h : H ⟶ G` be a
closed subgroup morphism. If `H` is smooth, connected and solvable, and the
range of `h` is normal on every test scheme, then `IsTorus H` and
`IsCentral h`. The centrality conclusion quantifies over every test scheme.
There is no restriction on the characteristic.

## Implemented proof

The proof applies the published
`algClosedReductiveNormalSolvableTorus_of_quotient` from
[`AlgClosedNormalSolvableTorusReduction`](AlgClosedNormalSolvableTorusReduction.md)
to the published exact theorem `solvableTorusQuotient` from
[`SolvableTorusQuotientProof`](../Absolute/SolvableTorusQuotientProof.md),
at the same universe `u`. Thus the quotient premise of the reduction is
discharged by a proof, and the resulting theorem has only the hypotheses of
the unchanged target.

The reduction first obtains an actual fppf quotient `q : H ⟶ D` by a smooth
connected unipotent closed subgroup `i : U ⟶ H`, with `D` a split torus.
The source `H` is affine because it is closed in the affine group `G`.
Conjugation by rational points of `G` preserves the range of `i ≫ h`:
the composite from `U` through each conjugate into `D` is trivial, since a
homomorphism from a unipotent group to a split torus is trivial.
Closed representability of the normalizer and reducedness of the smooth
group `G` then give normality of this range on every test scheme.

The trivial unipotent radical of `G` forces the range of `i ≫ h` to be
trivial. Since `h` is a monomorphism, the range of `i` is trivial as well.
The fppf quotient `q` is consequently an isomorphism, so `H` is a split
torus and hence a torus. Finally, the published
`isCentral_of_isNormal_of_isSplitTorus` makes the normal monic split torus
`h` central in the connected group `G`.

## Provenance

This is an internal composition of published proofs. Worker 1378 authored
the reduction, and Workers 1500 and 1492 authored the exact quotient proof.
The reduction Markdown explains its relation to the original source route
and its use of triviality of unipotent-to-torus homomorphisms. This module
introduces no additional structural assertion or source citation.
