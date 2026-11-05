# Proof of the proper solvable homogeneous quotient criterion

Author: Worker 281.

`properSolvableQuotientBorel` proves the published
`ProperSolvableQuotientBorelStatement.{u}` from
`Langlands.GroupScheme.Absolute.ProperSolvableQuotient`. That statement and
its imported definitions are unchanged.

## Statement proved

For every algebraically closed field `k`, in every universe and of any
characteristic, let `G` be a smooth connected affine group scheme over
`Spec k`. Let `i : H ⟶ G` be a closed subgroup with `H` smooth, connected
and solvable in the published sense (solvability of the group of geometric
points over `AlgebraicClosure k`). Let `q : G.X ⟶ Q` be an actual map to a
proper scheme `Q` over `Spec k`. Suppose `q` is smooth, surjective and
quasi-compact. Suppose also that on every test scheme, `g ≫ q = h ≫ q` holds
exactly when `g⁻¹ * h` lies in `SubgroupFunctor.range i`. Then `i` satisfies
the published `IsBorelSubgroup` predicate. No reductivity, characteristic or
other extra assumption is added.

## Implemented proof

The proof applies the published conditional reduction
`properSolvableQuotientBorel_of_solvableProperFixedPoint` to the published
unconditional theorem `solvableProperFixedPoint` from
`Langlands.GroupScheme.SolvableProperFixedPointProof`. That theorem proves
`SolvableProperFixedPointStatement.{u}` (task
`7b5e23b5-cf13-4e63-9bf0-2c70d78b0696`).

The reduction, documented in `ProperSolvableQuotient.md`, works as follows.
It chooses a Borel subgroup `B` of `G`. It descends the left multiplication
of `G` along `q` to an actual action on `Q`, and restricts this action to `B`.
`Q` is nonempty because `G` is connected and `q` is surjective. The
fixed-point theorem then gives a rational point of `Q` fixed by `B` on every
test scheme. This point lifts to a rational point `g` of `G`. The exact
fibres of `q` then show that the conjugate of `B` by `g⁻¹` factors through
`H`. That conjugate is Borel, so its maximality makes the factor an
isomorphism. Transport along this isomorphism shows that `i` is Borel.

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), Proposition 17.19, printed p.357
(one-based PDF p.373), implication (b) ⇒ (a). Registered source
`milne-2017-algebraic-groups`. Milne proves (b) ⇒ (c) ⇒ (a) through
Theorem 17.16 (printed p.356): by the fixed-point Corollary 17.3, a Borel
subgroup fixes a point of the complete quotient `G/H`, so one of its
conjugates lies in `H`. Maximality of that Borel among connected solvable
subgroups then gives equality. The implemented proof follows this route
directly. This module only composes two published theorems and adds no new
mathematical claim.
