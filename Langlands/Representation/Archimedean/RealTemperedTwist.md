# Determinant twists of real standard modules

This is an internal transport construction for
`RealTemperedStandardIrreducibleStatement`. Its input is a list `ds` of total
rank `n` and a real number `s`. It uses the existing `realBlockTwist s`, which
adds `s` to every block exponent.

`RealTemperedTwist.twistEquiv` is the complex linear equivalence on the
`O(n)`-finite functions obtained by multiplying by `|det g|^s`. Its inverse
multiplies by `|det g|^(-s)`. The maps into the standard modules, preservation
of their Fourier conditions and preservation of finite vectors are the proved
`RealLinkedJacquetStages.twK` construction; the inverse identities follow by
adding the two exponents.

The twist commutes with the `O(n)` action because an orthogonal determinant
has absolute value one. For the real matrix direction `X`, the product rule
shows that the target Lie operator on the twisted function equals the twist
of the source Lie operator plus `c_X` times the twisted function. Here `c_X`
is the right derivative of `|det|^s` at the identity. Multiplicativity of the
determinant power makes this the same scalar at every point. The proof does
not compute `c_X` as a trace.

These are derived transport facts about the Library's concrete function
model. They do not assume irreducibility, a Langlands quotient theorem or
the Langlands classification.
