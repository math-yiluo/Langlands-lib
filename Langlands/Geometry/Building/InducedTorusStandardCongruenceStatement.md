# First congruence subgroups of standard models of induced tori

Let \(F\) be a nonarchimedean local field, \(K=\texttt{inertiaFixedField}\ F\),
and \(\mathcal O=\texttt{fixedFieldIntegers}\ F\), with maximal ideal
\(\mathfrak m\). For an induced \(K\)-torus \(S\), the standard subgroup at
depth \(r\) is `localTorusFiltration F S hS r`. At zero it is the torus
Iwahori subgroup. At positive depths, `mem_localTorusFiltration_of_induced`
identifies membership with the geometric character inequalities for the
additive valuation normalized on \(F\).

`InducedTorusStandardCongruenceStatement` ranges over all nonnegative real
depths \(r\) and all smooth affine integral models \(M\) of \(S\) with
`M.integralPoints = localTorusFiltration F S hS r`. It asserts that
`M.congruenceSubgroup = localTorusFiltration F S hS (r + 1)` as subgroups of
\(S(K)\). Here `M.congruenceSubgroup` is the image of the kernel of reduction
from \(M(\mathcal O)\) to \(M(\mathcal O/\mathfrak m)\) under the specified
generic-fibre identification. The model is identified by its integral-point
image on the smooth affine models, as in the smooth model comparison of
`IntegralModel.smoothHomExtension`. The scope includes wildly ramified
induced tori and residue characteristic two.

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*
(Cambridge University Press, 2023), Proposition B.3.6(3) and its proof,
printed pp. 658–659 (one-based PDF pp. 689–690). On a Weil restriction
factor from a finite separable \(E/K\) of ramification index \(e\), a positive
depth \(r\) corresponds to the integral level \(\lceil er\rceil\). The first
congruence kernel over \(\mathcal O\) shifts this level by \(e\), since
\(\mathfrak m\mathcal O_E=\mathfrak m_E^e\), giving the level
\(\lceil e(r+1)\rceil\). At depth zero the same shift takes the full
coefficient unit group to level \(e\).
[Integral Models of Tori](https://doi.org/10.1017/9781108933049.026)

- Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`
- SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`
