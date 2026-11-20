# The degree of the rational division action on a formal module

Drinfeld 1976, §2 A, printed p. 109 (PDF p. 3), uses the normalized
order of the determinant on the division factor and the inverse division
unit in the framing formula. The determinant on this factor is the reduced
norm. The degree here is the positive rational ratio of actual finite
kernel ranks associated to the height formula in Harris 1997, Appendix,
printed p. 112 (PDF p. 38).

Let \(\pi\) be a uniformizer of the local integer ring. For an order
action on a formal module over a coefficient field, assume
`IsPiDivisible π` for the underlying formal module. This supplies the fppf
local lifting and finite locally free kernels for the scalar powers used
in the rank ratio. Applying the rational degree character to the extended
division action gives a character of the division units. An integral
order unit acts by an integral isomorphism and has degree one. Under
`HasPiHeight π q H`, the central scalar \(\pi\) acts by the original
scalar endomorphism with kernel rank \(q^H\), which is its degree.

Write \(d\) for the reduced degree and suppose the scalar height is
\(Hd\) with rank base \(q>0\). The order-one scalar uniformizer raised to
minus the reduced-norm order of \(g\) corrects \(g^d\) into an integral
unit. Applying the degree character and using injectivity of positive
\(d\)-th powers yields \(q^{H\operatorname{ord}(\operatorname{Nrd}(g))}\).
The actual forward map to the inverse-conjugated order has the negative
exponent because its underlying rational map is the action of \(g^{-1}\).
