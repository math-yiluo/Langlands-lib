# Base change and fpqc detection of ordered multiplication

This internal construction treats an arbitrary finite ordered family of
homomorphisms into a group scheme. It uses the original
`RelativeRoot.orderedMultiplication`, with its specified order, without
commutativity or subgroup hypotheses.

`finiteProductBaseChangeIso` compares the actual pullback of the categorical
finite product with the categorical finite product of the pullbacks. The
index universe is independent of the scheme universe. The underlying
product fan is limiting because group objects create limits; the scheme
pullback functor preserves that limit. Uniqueness of limit objects supplies
the isomorphism. Its forward and inverse maps satisfy the displayed
projection equations.

`orderedMultiplication_baseChange` identifies the pullback of the original
ordered multiplication with the ordered multiplication of the pulled-back
inclusions after this canonical comparison. The proof uses the original
list product in index order. Monoidal pullback preserves products and units
in each point-group Hom set, so this also covers `Fin 0`.

Invertibility therefore survives arbitrary base change. Conversely, for an
fpqc base morphism, the pullback square of the original underlying scheme
morphism and the published fpqc descent theorem for isomorphisms reflect
invertibility. Reflection from schemes to schemes over the base gives
`isIso_orderedMultiplication_baseChange_iff`. The field-extension corollary
uses the established faithfully flat quasi-compact spectrum map of any
field extension.

The provenance is internal: finite-product universal properties,
monoidal pullback, and fpqc descent of scheme isomorphisms. This proves the
geometric detection step for any supplied factors. It does not identify
the base change of a semigroup subgroup with the semigroup subgroup of a
pulled-back action, compare the action weight supports, construct a
compatible solvable decomposition, or prove the full
`SemigroupOrderedProductStatement`.
