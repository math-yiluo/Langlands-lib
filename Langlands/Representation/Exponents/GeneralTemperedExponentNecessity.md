# Upper exponent bound for a general analytically tempered source

`Langlands.GeneralTemperedExponentNecessity.upperBound` says that for
positive rank, `T.IsTempered π`, an actual upper Jacquet exponent
`hχ : T.IsJacquetExponent B π χ`, and a tuple `a` whose normalized absolute
values are increasing, one has `‖(χ a : ℂ)‖ ≤ 1`.
The field and source universes are independent. No irreducibility,
finite generation, finite length or tensor factorization of `π` is assumed.

The generalized eigencharacter supplies a nonzero vector in the actual
Jacquet quotient. Surjectivity of `B.jacquetMk` supplies a nonzero source
vector, giving a `Nontrivial` instance for the source carrier. This is used
when proving that its unitary central character has open block-scalar
kernel.

The published `ScalarLayer.oneBlockLeviEquiv` identifies the actual one-block Levi continuously with
the ambient general linear group by evaluation at its unique coordinate.
The proof pulls `π` back along this equivalence. It chooses a Borel Haar
measure on the ambient quotient by the full center and transports it to
the one-block quotient. The published
`isTemperedModCenter_comp_continuousMulEquiv` gives the analytic predicate
for the transported representation and measure.

For every refinement of the one-block shape, the published
`ProductLeviNecessity.norm_le_one_of_diagonal` gives the proper test-cut
bounds, and `norm_le_one_of_mem_center` gives the full-center test bound.
`norm_le_one_of_test` combines these into the necessary bound for all
increasing tuples in that refinement. These helper lemmas require the
analytic tempered predicate, without requiring an irreducible carrier.
Finally, the published
`ProductLeviTemperedFactorization.jacquetExponent_bound_of_core` transfers
the refined bound back to the original upper Jacquet exponent through the
actual one-block identification.

This is an internal adapter of published results, adapted by Worker 1008
from Worker 429's `UpperTemperedNecessityProbe`. Worker 349 independently
developed the same necessary-exponent composition. The one-block adapter
follows the published scalar-layer adapter of Worker 851, while the
analytic estimates are the published work of Workers 819 and 219. The
module imports those estimates directly and reuses the published one-block
equivalence. It proves the necessary
inequality only and does not use the unproved
`GLTemperedExponentCriterionStatement` or a converse criterion.
