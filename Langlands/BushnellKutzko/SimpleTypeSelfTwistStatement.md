# The unramified stabilizer of a supercuspidal representation containing a simple type

`SimpleTypeSelfTwistStatement` takes an irreducible supercuspidal smooth
\(\pi\) of \(\mathrm{GL}_n(F)\) containing a simple type \((J,\lambda)\)
with exhibiting data of parameter field \(E\). Here \(F\) is any
nonarchimedean local field and \(n>0\), with independent field and carrier
universes. For an unramified quasicharacter \(\chi\) of \(F^\times\), the
determinant twist is equivalent to \(\pi\) exactly when \(\chi\) has
finite order dividing \(n/e(E\mid F)\). The order is the order of the
homomorphism in the character group with pointwise multiplication.
The ramification index is `subfieldRamificationIndex` for the parameter
field of the exhibited data. At level zero \(E=F\), so the test is
\(\chi^n=1\).

The proof in the source uses the chosen type in \(\pi\), compact induction
from its \(E^\times J\) and the restriction of the determinant to
\(E^\times\). In particular, its reference to the hypotheses of Theorem
(6.2.4) requires only the single exhibited type for this assertion.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), (6.2.5), printed pp. 204–205, and the level-zero
convention following (5.5.10), printed p. 185.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
