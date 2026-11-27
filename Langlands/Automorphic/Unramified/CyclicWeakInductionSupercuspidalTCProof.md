# Unique-place supercuspidality over a totally complex base

`cyclicWeakInductionSupercuspidalTC` proves
`CyclicWeakInductionSupercuspidalTCStatement.{uF,uE,uV,uW}`. The two field
universes and the two spectral-presentation universes remain independent.
The cyclic extension of the totally complex base is itself totally complex.
Over each field the equal-rank coverage of the complex ordinary normalized
integrals gives nonzero archimedean tests. Realization of the specified
Whittaker models, quotient-product integration and the complex local
functional equation give the equal-rank semi-local equation through
`equalSemilocalEquationTC_of_ordinaryGeneration`.

The proof applies `cyclicWeakInductionSupercuspidalFromEqualSemilocalTC` to the
two equations. The ordinary and reflected cofinite orbit Euler identities
compare the self-pair of the supplied weak induction with the pairs of the
upper representation and the duals of its arithmetic conjugates. Two
determinant-character twists isolate the order of the certified local
gamma factor. At the distinguished finite place the upper fibre is a
singleton. The arithmetic comparison identifies the actual conjugate
components there, and the nonidentity conjugates have different smooth
classes from the original. Thus the identity summand contributes order
one at zero, the remaining summands contribute zero there, and no
summand has positive order at another real point. The self-pair
criterion gives supercuspidality for the actual weak induction.

This implements the two-twist order comparison in Henniart and Herb,
*Automorphic induction for GL(n) (over local non-archimedean fields)*
(1995), Lemma 8.13 and §§8.14–8.17, printed pp. 179–184, and the
supercuspidality argument of Proposition 5.5, printed pp. 152–153,
used in Harris (1998), proof of Proposition 4.8, printed p. 203.
