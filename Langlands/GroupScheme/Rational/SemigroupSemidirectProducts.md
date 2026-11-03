# Exact ordered semigroup products under a semidirect lift

This internal module works over any field and at arbitrary universe `u`.
It starts with an actual action of a smooth connected affine group `K` on a
smooth connected affine group `G`, and a commuting action of a split torus
`S` on `G`. The external action is lifted to the actual semidirect product
and fixes its acting coordinate.

If zero is absent from the full intrinsic ambient support, support
containment forces the trivial `S`-action on `K` to have empty support:
its only possible weight is zero. The smooth connected empty-support
triviality theorem makes the top subgroup of `K` equal to the identity
subgroup, on every test scheme. Thus each acting point is the identity.
These results need smoothness and connectedness only of `K`.

The canonical inclusion of `G` into the semidirect product is then bijective
on points for every test scheme. Its monicity gives injectivity, and the
actual normal/acting point decomposition gives surjectivity. Yoneda supplies
the scheme isomorphism `semidirectNormalIsoOfZeroNotMem`, whose forward map
is precisely that inclusion. Its all-test range is top.

`hasOrderedSemigroupProducts_semidirect` assumes the existing global
`SemigroupFunctorialityStatement` and `SemigroupIntersectionStatement`, and
the exact ordered-product property for the action on `G`. The normal-factor
support lies in the actual full ambient support, so the larger-support
restriction theorem supplies normal factors for the original ambient
partition blocks without changing their order.

When zero occurs, the imported all-semigroup inner-stability theorem
discharges the stability premise of the semidirect ordered assembly. The
original zero-containing block absorbs the acting factor. When zero does
not occur, the normal inclusion is an isomorphism with range top.
Closed-inclusion semigroup transport identifies every exact ambient factor
with the image of its normal factor, even if a block's positive closure
contains zero. Postcomposition by that inclusion preserves the actual
ordered multiplication and its isomorphism property.

The partition condition remains the exact cross-exclusion of one original
block from the positive additive-semigroup closure of another. No
disjointness of generated closures is assumed. The proof includes arbitrary
original order and `Fin 0`.

This is a derived assembly from the imported actual constructions. It
retains the global functoriality and intersection premises. It constructs
no solvable decomposition or scalar descent and does not prove the full
`SemigroupOrderedProductStatement`.
