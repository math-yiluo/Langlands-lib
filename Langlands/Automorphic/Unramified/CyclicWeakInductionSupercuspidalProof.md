# Unique-place supercuspidality of cyclic weak automorphic induction

`cyclicWeakInductionSupercuspidal` proves the unrestricted
`CyclicWeakInductionSupercuspidalStatement.{uF,uE,uV,uW}`. It retains the
two independent field universes, the two independent presentation universes,
and the positive-rank convention of the statement.

Over each of the two number fields, `equalSemilocalEquationFromOrdinaryTests`
uses the real and complex ordinary equal-rank place tests. At real places,
`realEqualOrdinaryPlaceTestsPositiveRank` supplies the tests by descent to
`GL₁(ℝ)` and Mellin inversion. At complex places, the coverage part of
`complexOrdinaryNormalizedGeneration`, together with
`complexWhittakerRestrictionOnto`, supplies the tests. The semi-local
reduction includes the rank-one Tate integrals, carries nonvanishing through
the local functional equations, and applies quotient-product factorization.

`cyclicWeakInductionSupercuspidalFromEqualSemilocal` applies the resulting
equations to the supplied weak induction and its contragredient downstairs,
and to the original representation paired with the contragredients of its
arithmetic orbit upstairs. The ordinary and reflected cofinite spherical
Euler products match. Two norm-related determinant-character twists isolate
the order of the finite local gamma factor at the distinguished place. The
unique-place hypothesis reduces the upstairs sum to that fibre, where the
completion comparison and arithmetic transport identify the supplied local
factors of the conjugates.

The identity summand gives a simple zero at zero. Every nonidentity summand
has order zero there by its distinct supercuspidal class. All summands have
nonpositive order at every other real point. The self-pair gamma-order
criterion therefore gives a supercuspidal component for the supplied weak
induction with its irreducible admissible local presentation.

The cofinite factor comparison and the two twists implement Henniart and
Herb, *Automorphic induction for GL(n) (over local non-archimedean fields)*
(1995), Lemma 8.13 and §§8.14–8.17, printed pp. 179–184. The order argument
uses the supercuspidality test underlying Proposition 5.5, printed
pp. 152–153, as applied in the non-singleton branch of Harris (1998),
Proposition 4.8, printed p. 203.
