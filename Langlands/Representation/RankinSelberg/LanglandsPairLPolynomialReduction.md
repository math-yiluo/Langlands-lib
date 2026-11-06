# Preserving a fixed L-polynomial through Langlands data

Authors: Worker 1753 and Worker 1748.

This internal reduction assumes regular Langlands-data uniqueness and promotes
one supplied standard-module L-polynomial to the existing
`IsLanglandsPairLPolynomial` relation. The field and the two original block
carrier universes are arbitrary and independent. Every conclusion retains the
same polynomial `P`; the construction does not choose another polynomial.

`standardModule_equiv_of_regular_uniqueness` raises each input tempered datum's
block carriers to the maximum of its original carrier universe and the field
universe, using `TemperedLanglandsDatum.universeLift`. The supplied
`universeLiftStandardModuleEquiv` transports the same irreducible quotient to
each lifted standard module. The existing
`standardModule_iso_of_regular_uniqueness` compares those lifted standard
modules using the assumed regular-data uniqueness. Composing its actual
representation equivalence with the two lift equivalences gives an equivalence
between the original standard modules.

`isLanglandsPairLPolynomial_of_standardModule` uses the two supplied tempered
data as the existential presentation witnesses. For any other presentations of
the same pair, the preceding comparison gives standard-module equivalences.
`IsPadicSymmetricLPolynomial.congr_equiv` transports the original certificate
along those equivalences. This proves the universal clause of the relation.

`isLanglandsPairLPolynomial_of_saturatedData` starts with tempered blocks in the
maximum of the field and original carrier universes. It uses
`TemperedLanglandsDatum.exists_realization` to obtain equivalent individual
irreducible blocks in each original carrier universe. The resulting
standard-module equivalences transport the quotient witnesses and the fixed
polynomial certificate. The preceding theorem then proves the relation with its
original carrier universes.

`langlandsPairLPolynomialOfFixedSaturatedData` packages the supplied polynomial
and this last certificate as the subtype of certified Langlands polynomials.
Its polynomial value is definitionally the supplied `P`.

The provenance is internal and derived from `LanglandsLFactor`,
`LanglandsDatumRealization`, the actual irreducible-quotient transport law, and
the equivalence invariance of the integral-based L-polynomial. Worker 1748
authored the reused carrier-realization infrastructure. This reduction proves
neither regular-data uniqueness nor an analytic factor product formula, and it
does not by itself prove `SquareIntegrableDataLFactorStatement`.
