# Equivariant maps between affine finite free action quotients

This is an internal categorical consequence of the effective finite free action
quotients constructed in the preceding module. It supports the cross-tuple
construction motivated by Stacks Lemma 68.8.3 (Tag 0BBN), first proof paragraph,
registered source `stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The quotient input comes through the previously proved specialization of Stacks
Proposition 39.23.9 (Tag 03BM), registered source
`stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`.
The present categorical calculation is derived rather than quoted from those
sources. It introduces no existence assumption for a quotient or approximation.

`isPullback_of_fpqc_kernelPair` treats a commuting square of schemes whose map
from the upper left object to the lower left object is faithfully flat and
quasi-compact. Its two supplied squares are that map's actual kernel pair and
the desired square after pullback along that cover. The proof factors the square
through its canonical pullback. The second supplied square identifies the
pullback of this comparison morphism with an isomorphism. Pasting with the first
square and faithfully flat descent of isomorphisms show the comparison itself is
an isomorphism. Thus the original square is cartesian.

For free actions `A` and `B` of the same finite group on schemes `X` and `Y`, and
an equivariant morphism `f : X ⟶ Y`, `equivariantRelationMap` is the coproduct of
copies of `f`. Its source and target equations are
`equivariantRelationMap_source` and `equivariantRelationMap_target`. The source
equation needs no equivariance assumption; the target equation does.
`equivariantRelationMap_isPullback_target` states that its square on the first
endpoints is cartesian. Each summand is a commuting square with the two
horizontal maps action isomorphisms. Pullbacks distribute over the finite
coproduct of these squares.

When both schemes are affine and `Q` and `Q'` are their actual affine quotients,
`quotientMap` descends the invariant morphism `f ≫ Q'.map` to the quotients.
`map_quotientMap` gives its factorization equation.
`quotientMap_isPullback` shows that the equivariant map and the two quotient maps
form a cartesian square. The proof pastes the cartesian square of relation maps
with the effective kernel pair of `Q'`, then applies
`isPullback_of_fpqc_kernelPair` with the kernel pair and finite étale surjective
cover `Q.map`. The schemes and finite group live in arbitrary common universe
`u`. No assertion about cross-tuple strata or Noetherian approximation is made.
