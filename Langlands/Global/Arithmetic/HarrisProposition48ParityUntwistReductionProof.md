# Two-place Harris parity untwisting from auxiliary untwisting

`Langlands.Global.Harris.proposition48ParityUntwistReduction` proves
`Proposition48ParityUntwistReductionStatement.{uF, uV}` for independent local-field
and representation-carrier universes. This is the conditional two-place step in the
[parity reductions](HarrisProposition48ParityReductionStatement.md) for Harris
(1998), Proposition 4.8, not a separate assertion in the source.

The private lemma `auxiliaryValidAtParity` projects full validity to auxiliary
validity by omitting the primary-place clauses and the conditions comparing the
places. The proof uses it on the raw datum at parity `b` and on the corrected datum
at rank parity `[E' : E] − 1`. The auxiliary normalization keeps all three
conditions on the same base character `ν`. Replacing the corrected primary
character `χ` by `χs` changes neither auxiliary validity nor the corrected
`IsSolution` predicate: the latter uses the same global inducing character,
base field, and auxiliary place.

Applying the supplied auxiliary untwist to that normalization and the same
corrected class `c` gives the actual realizations `S` and `T`, with `T.isoClass = c`.
Both conclusions require exactly the same `IsUntwistedSolution` on the original
datum, so the witnesses and their determinant-multiplier relation are returned
unchanged. Regular algebraicity is required of `T`, not `S`.
