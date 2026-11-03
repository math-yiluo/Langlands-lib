# Cocharacters factor through the fixed torus envelope

Worker 1436. This internal adapter works at arbitrary universe `u` over every
field `k`. Let `G` be an actual group scheme over `Spec k` with affine structure
morphism, and let `D : TorusGeneratedEnvelope G` represent the existing fixed
`closedTorusEnvelope G`. Smoothness and connectedness of `G` are unnecessary.
All images and equalities of subgroup functors use every relative test scheme,
including nonreduced tests.

`IsSplitTorus.range_le_closedTorusEnvelope` shows that the image of any actual
homomorphism `f : T.toGrp ⟶ G` from a split commutative torus lies in the fixed
envelope. No closedness or injectivity of `f` is assumed. The proof applies the
published `IsSplitTorus.exists_factor_isSplitSubtorus` to obtain an actual closed
split-torus inclusion `i` and a factor `p` with `p ≫ i = f`. A split torus is a
torus, so the envelope contains the image of `i`. Composing each test point with
`p` proves the claimed containment for `f`.

`TorusGeneratedEnvelope.splitTorusFactor` applies the existing represented
subgroup factorization to this containment. `splitTorusFactor_comp` proves that
its composite with `D.inclusion` is the original `f`, and
`splitTorusFactor_unique` proves uniqueness using the monomorphism in
`D.represents`. Thus this extends the envelope's existing factorization of
closed torus inclusions to arbitrary homomorphisms from split tori.

`cocharacterFactor` specializes the construction to the actual multiplicative
group, using `isSplitTorus_gm`. `cocharacterFactor_comp` and
`cocharacterFactor_unique` give its factorization equation and uniqueness for
every supplied cocharacter, including the trivial cocharacter.

The three lemmas `parabolic_cocharacterFactor`, `unipotent_cocharacterFactor`,
and `centralizer_cocharacterFactor` identify the dynamic functors for the
factored cocharacter with the preimages of the ambient dynamic functors under
`D.inclusion`. Their proofs apply the existing closed-subgroup restriction
theorems in `Dynamic.ClosedSubgroup` and rewrite the cocharacter factorization
equation. These equalities hold on all relative tests.

The provenance is internal: these are consequences of the published split-torus
image theorem, the fixed envelope's universal property, and the published
closed-subgroup restriction theorems. No new literature theorem is asserted.
This supplies the cocharacter factorization and dynamic intersection step
needed in the torus-envelope reduction of pseudo-parabolic rational lifting.
It proves neither existence or normality of the envelope, rational-point
density, a quotient comparison, nor the full rational-lifting theorem.
