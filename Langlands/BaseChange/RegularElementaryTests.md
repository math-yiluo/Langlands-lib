# Regular elementary tests for cyclic base change

`regularElementaryBaseChangeTests` constructs the regular Labesse pair of
Schwartz–Bruhat functions for the cyclic unramified extension \(E/F\) of
p-adic fields, in rank \(r+1\). For a strictly decreasing weight \(\nu\),
use the base uniformizer \(\varpi\) and its image in \(E\). On the upper
group the function is the indicator of the set
\[
\{k^{-1} \operatorname{diag}(\varpi^{\nu_i}) m\,\sigma(k)
       : k\in K_E,\ m\in T(\mathcal O_E)\}.
\]
On the lower group use ordinary \(K_F\)-conjugation and the weight
\(\ell\nu\), where \(\ell\) is the cyclic degree. Here \(K_E,K_F\) are the
actual spherical subgroups and \(T(\mathcal O)\) consists of the
diagonals with entries in the integral-unit subgroup. The two evaluation
lemmas state the exact characteristic functions, with value one on the
specified sets.

The support is a continuous image of the compact subgroup times the
product of the translated integral-unit sets. The diagonal tuples range
over an open subset of the scalar coordinate space. If the off-diagonal
equation \(a_i\sigma(z)=a_jz\) had a nonzero solution, applying the
normalized additive order would give \(\nu_i=\nu_j\), because the
automorphism preserves order. `isOpen_twistedDiagonalSaturation` then
gives openness. The unramifiedness equality makes the image of
\(\varpi\) a uniformizer, and positivity of the cyclic degree keeps
\(\ell\nu\) strictly decreasing. The lower test is the same construction
with identity twist.

The definition uses the regular case of Henniart–Lemaire, *Changement de
base et induction automorphe pour GL(n) en caractéristique non nulle*
(2011), I.4.1–I.4.2, pp. 26–28. The strict-weight scope and the choice
of the scaled ordinary partner are used in I.5.5 and I.6.7.
