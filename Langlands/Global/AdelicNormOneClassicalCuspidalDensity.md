# Transfer of classical cuspidal density to the norm-one quotient

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

For each proper rational parabolic, a dynamic presentation by a rational
cocharacter gives a geometric representative of the canonical radical.
The period over that representative is the canonical normalized period.
The positive rational quotient is homeomorphic to the norm-one rational
quotient with exactly the transported Haar measure. On the norm-one group
the positive-quotient pullback equals the original function. Each
canonical proper radical lies in that group, so the pointwise periods of
the positive-quotient representative at norm-one arguments vanish. The
period at an arbitrary argument is the period at its norm-one projection.

Rapid decay on a finite-translate cover gives a square-integrable class of
the original restricted function, and the period identities put its
transported class in full cuspidal `L²`. The Hilbert density theorem gives
a continuous positive-quotient representative whose adelic pullback is
classical, cuspidal and of uniform derivative growth. Measure preservation
identifies the Hilbert distance with the norm-one `L²` seminorm of the
difference, giving the requested approximation.

The transfer supplies the norm-one density step used in the continuous
version of Mœglin–Waldspurger I.3.4, p. 46.
