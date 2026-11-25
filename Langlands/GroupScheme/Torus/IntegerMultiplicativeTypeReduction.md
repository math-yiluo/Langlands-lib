# Integer diagonalizability from normal-base isotriviality

This internal reduction preserves the actual group scheme and the original
integer base. Its last theorem explicitly takes
`Langlands.GroupScheme.MultiplicativeTypeNormalIsotrivialStatement` as a
hypothesis; this file does not prove that general statement.

`RelativeMultiplicativeType.IntegerDiagonalizabilityFromNormalIsotrivialStatement`
is the Prop-valued statement of that implication, in every universe.
The theorem `integer_isDiagonalizable_of_normalIsotrivial` proves its
conclusion for each supplied group and multiplicative-type hypothesis.

`RelativeMultiplicativeType.IsDiagonalizable.of_section` pulls a given
diagonalizable model back along a section of the covering morphism.
The comparison of iterated pullbacks and the identity pullback identifies
the resulting group scheme with the original group scheme. Diagonalizability
is transported across that actual group-scheme isomorphism.

`RelativeMultiplicativeType.isDiagonalizable_of_finiteEtale_integer`
applies the section theorem from `IntegerFiniteEtaleSection` to a supplied
finite, étale, surjective morphism to the lifted integer spectrum.
It then applies the general section argument.

`RelativeMultiplicativeType.integer_isDiagonalizable_of_normalIsotrivial`
uses the irreducible-base clause of the supplied normal-base isotriviality
statement. The lifted integer spectrum is irreducible because its ring
is a domain. Its actual structure-sheaf stalks are integrally closed
domains by the published `spec_hasNormalStalks`: the lifted integer ring
is integrally closed by transport from the integers. The resulting finite
étale surjective morphism gives the preceding theorem.

This supplies the arithmetic application in Conrad, *Reductive group schemes*
(2014), Corollary B.3.6 and its integer example, p.293 (registered source
`conrad-2014-reductive-group-schemes`). It is derived from the published
relative diagonalizable base-change and affine integer arithmetic helpers.
The additional assertion that a diagonalizable relative torus is a finite
split torus, and a proof of the general normal-base statement itself, are
separate inputs needed for the final integer-torus theorem.
