# Transfer of classical cuspidal density to the norm-one quotient

`Langlands.Global.positiveQuotientOfNormOneRestriction` restricts a continuous,
left rational-invariant function to the norm-one group and transports its
descent along `positiveQuotientHomeomorph`. The resulting continuous function on
the positive rational quotient agrees with the given function on norm-one
representatives, by `positiveQuotientOfNormOneRestriction_mk`.

If the original function has zero proper constant terms, any `L²` class
represented by the transported function belongs to the full cuspidal submodule
by `mem_fullAEL2CuspidalSubmodule_of_normOneRestriction`. For each proper
rational parabolic, a dynamic presentation by a rational cocharacter gives a
geometric representative of the canonical radical. The period over that
representative equals the canonical normalized period. Every proper radical
lies in the norm-one group, so the period integrands agree at norm-one
arguments. The period of the transported function at any adelic argument is
its period at the norm-one projection. The theorem
`groupSchemeFullAEL2ContinuousCuspidality` converts this pointwise vanishing to
membership in full cuspidal `L²`.

`Langlands.Global.adelicNormOneClassicalCuspidalDensity_of_centerConjugation`
proves `AdelicNormOneClassicalCuspidalDensityReductionStatement`. It derives
`AdelicNormOneClassicalCuspidalDensityStatement` from triviality of
archimedean conjugation on the enveloping center. In particular, the
approximation applies over a number field to an affine locally finite-type
connected reductive group with a supplied smooth relative dimension, any
compact subgroup at infinity and a positive-size closed matrix embedding.
The input is a rational-invariant function smooth on each archimedean slice
with one common open right level at the finite adeles. It has all proper
periods zero and one common height exponent for its archimedean derivative
words.

Rapid decay on a finite-translate cover gives a square-integrable class of
the original restricted function. The transfer theorem puts its
transported class in full cuspidal `L²`. The Hilbert density theorem gives
a continuous positive-quotient representative whose adelic pullback is
classical, cuspidal and of uniform derivative growth. Measure preservation
identifies the Hilbert distance with the norm-one `L²` seminorm of the
difference, giving the requested approximation.

The transfer supplies the norm-one density step used in the continuous
version of Mœglin–Waldspurger I.3.4, p. 46.
