# Tangent coordinates of a multiplicative Weil restriction

Let \(R\) be a commutative ring and \(B\) a commutative \(R\)-algebra that is
finite projective as an \(R\)-module. Write \(W_B=\operatorname{Res}_{B/R}\mathbf
G_m\) for `WeilGm.groupScheme`. Combining `WeilGm.affineUnitsEquiv` with
`DualNumberBaseChange.tensorEquiv` identifies \(W_B(R[\varepsilon])\) with
\(B[\varepsilon]^\times\). This is `WeilGm.dualUnitsEquiv`. Naturality in the
test algebra identifies reduction to \(W_B(R)\) with taking the constant
coefficient after the identification \(B\otimes_R R\simeq B\).

`WeilGm.lieCoefficientEquiv` sends the actual Lie module
`Additive (lieKernel W_B R)` to \(B\) by taking the
\(\varepsilon\)-coefficient. The reduction condition gives constant
coefficient \(1\), so the unit representing \(x\) is \(1+\varepsilon b\),
where \(b\) is `WeilGm.lieCoefficientEquiv R B x`. The equality is
`WeilGm.dualUnitsEquiv_lieCoefficientEquiv`. Multiplying two such units adds
their coefficients because \(\varepsilon^2=0\). The tensor comparison
intertwines the Lie module's epsilon-scaling action with scalar multiplication
on \(B\). The two coefficients determine the point, and every \(b\) occurs
because \(1+\varepsilon b\) has inverse \(1-\varepsilon b\).

For another finite projective commutative \(R\)-algebra \(C\) and an
\(R\)-algebra map \(f:B\to C\), `WeilGm.lieCoefficientEquiv_coefficientMap`
identifies `Lie.targetMapLinear (WeilCongruence.coefficientMap f) R` with \(f\)
under the two equivalences. The proof transports the action \(f\otimes 1\) on
global-section coordinates to the affine test algebra. Naturality of the
dual-number tensor comparison then applies \(f\) to both coefficients,
sending \(1+\varepsilon b\) to \(1+\varepsilon f(b)\).

Kaletha–Prasad use the Lie identification for induced tori in the proof of
Proposition B.6.9 of *Bruhat–Tits Theory: A New Approach* (2023), printed
pp. 673–674 (one-based PDF pp. 704–705). The general finite projective
calculation and its coefficient-map formula follow from the affine point
functor of the Weil restriction and the dual-number description of the Lie
module.

- Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`
- SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`
