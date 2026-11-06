# Products over equal-exponent Langlands groups

Author: Worker 1748.

`SquareIntegrableFactorGrouping` packages the part of an actual
equal-exponent grouping used to compute factors: square-integrability of the
unitarily normalized original blocks, tempered data with matching exponents,
a shape and fiber equivalence for every group, rank equalities, actual group
representation equivalences from normalized induction, and the actual isomorphism between the
total inductions. The constructor `squareIntegrableFactorGrouping` extracts
these witnesses from `SquareIntegrableEqualExponentGrouping`, which remains an
explicit premise. The monotonicity witnesses are not needed in this computation.

`normalizedProductInduction_equiv_iff` identifies the representation of the
bundled induction functor with raw normalized induction. This is a definitional
identity, proved once for arbitrary bundled blocks before specializing to the
rank-transported normalized blocks.

For each group, `normalizedBlocks_hypotheses` transports irreducibility,
square-integrability and the invariant positive form along the supplied rank
equalities. `originalIndexEquiv` identifies the sigma type of all group indices
with the original indices by the fiber equivalences. The group exponent equals
the exponent of every block in its fiber.

`pairProduct` applies the conditional common-real-twist product formula to the
two families of normalized blocks and transports it through their actual group
equivalences. The common exponent then cancels each original block's negative
twist, including its rank transport. This gives the factor relation on the
original blocks and the finite product identity.

`product` applies the Langlands-type product formula to the two tempered
groupings. Uniqueness of each pair L-polynomial identifies its group factor
with the product computed by `pairProduct`. The two total-fiber equivalences
then pull the local polynomial families back to the original indices; the
finite-product reindexing lemma gives exactly the original double product.
Its polynomial still belongs to the standard modules of the grouped tempered
data.

These are internal consequences of the imported grouping definition,
normalized-block transport lemmas and grouped-factor adapters. The analytic
tempered and Langlands-type product formulas and existence of equal-exponent
grouping remain premises. This module does not supply a closed proof of JPSS
Theorem (9.5).
