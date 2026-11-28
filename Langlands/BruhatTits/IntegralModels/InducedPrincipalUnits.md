# Principal-unit quotients in induced torus coordinates

The proof of Kaletha–Prasad Proposition B.6.9 starts with the map
\(w\mapsto w-1\) on principal units of a split torus and applies it
to each coefficient field of a finite product of Weil restrictions.
This module implements the coefficient calculation from the split and induced
paragraphs of that proof in *Bruhat–Tits Theory: A New Approach* (2023),
printed pp. 673–674 (PDF pp. 704–705).

- Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`
- SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`

For a commutative ring \(C\) and an ideal \(J\), `WeilCongruence.principalUnits`
is the kernel on units of \(C\to C/J\). An element belongs to it precisely
when its difference from one belongs to \(J\). If \(J^2\subseteq L\),
`WeilCongruence.principalUnitDifference` takes that difference modulo
\(J\cap L\). The Lean denominator is the comap of \(L\) along the inclusion
\(J\hookrightarrow C\). The `Multiplicative` type synonym gives the additive
quotient the group notation used by the homomorphism. Multiplicativity follows
from
\[
ww'-1=(w-1)+(w'-1)+(w-1)(w'-1).
\]
The kernel is the subgroup of numerator units which reduce to one modulo
\(L\), written `(principalUnits L).subgroupOf (principalUnits J)`. If \(J\)
lies in the Jacobson radical of \(C\), each representative \(x\in J\) lifts to
the unit \(1+x\). The first isomorphism theorem gives
`WeilCongruence.principalUnitDifferenceEquiv`, and
`WeilCongruence.principalUnitDifferenceEquiv_mk` identifies the image of the
class of \(w\) with the class of \(w-1\).

`InducedTorusShallow.depthPrincipalUnitEquiv` uses the product of integral
coefficient rings in intermediate fields of the separable closure over the
maximal unramified field of a nonarchimedean local field. It uses the
normalized depth ideals \(J_r\) from `InducedTorusShallowIntegers`. For
\(x,y\in J_r\), additivity of the valuation on products gives each
coordinate of \(xy\) depth at least \(2r\). This proves
\(J_r^2\subseteq J_s\) for \(s\le 2r\). For \(r>0\), the fact that \(J_r\)
is an ideal gives every component of \(xy\) positive depth for \(x\in J_r\)
and \(y\in C\). The nonarchimedean valuation then gives multiplicative
value one to every component of \(1+xy\), so this tuple is a unit. The
Jacobson radical criterion gives \(J_r\subseteq\operatorname{Jac}(C)\).

The construction uses nonnegative real depth parameters and works in
equal and mixed characteristic. If \(r\le s\), the coordinate inequalities
give \(J_s\subseteq J_r\), so the quotients are \(U_{J_r}/U_{J_s}\) and
\(J_r/J_s\). This includes \(r=s\). The representative formula in these
coordinates is `InducedTorusShallow.depthPrincipalUnitEquiv_mk`.
