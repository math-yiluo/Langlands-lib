# Exact integral equations for prescribed rational multiples

This is an internal consequence of the localization equality criterion in
`Langlands.CategoryTheory.RationalizationDenominators`. It concerns any
preadditive category and requires no injectivity of its integral-to-rational
Hom map.

For integral morphisms `f` and `g` and a prescribed rational number `q`,
`IntegralMultipleData f g q` records integers `left` and `right`, a proof that
`left` is nonzero, the exact scalar identity
`right = left * q` in the rationals, and the actual integral equation
`left • f = right • g`. The right integer is also nonzero when `q` is nonzero.

`ofHom_eq_smul_iff_nonempty_integralMultipleData` proves that this data exists
exactly when `ofHom f = q • ofHom g`. To construct it, multiply the rational
equation by the positive denominator of `q`. Rationalization then identifies
the two integral maps `q.den • f` and `q.num • g`. The localization equality
criterion supplies a further nonzero integer annihilating their discrepancy.
Multiplying both numerator and denominator by that integer gives the exact
integral equation and preserves the prescribed ratio. Conversely, rationalize
the integral equation and cancel the nonzero rational scalar `left`.
`integralMultipleData` chooses data from the proved existence.

`IntegralMultipleData.map` transports supplied data through any additive
functor, preserving both integers and their ratio. This construction does not
identify independently chosen witnesses, infer integral equality from rational
equality, or assert any geometric isogeny or representability result.
