# Archimedean character presentations

Internal derived support for the actual Hecke target. This module constructs the
nonzero real and complex scales of nontrivial continuous additive characters,
using the covering-lift parameter lemmas. The complex trace is `2*re`, so the
real-linear phase coefficients `c,d` give the complex scale
`c/(4*pi) - i*d/(4*pi)`. Nontriviality excludes a zero scale.

The selected scales come with their defining pointwise formulas.
`realExponentialUnit` is the positive exponential as an actual real unit and is
continuous and multiplicative in the additive variable.

`exists_realCharacterParameters` proves that every actual continuous
quasicharacter of the real units has the form
`sign(x)^p * |x|^c`, for `p : Fin 2` and `c : ℂ`. Pulling the character back along
`realExponentialUnit` gives a continuous nonzero multiplicative function on the
additive real line, so the exponential parameter theorem applies. For positive
units, the real logarithm and the definition of complex powers give the claimed
formula. The value at `-1` squares to one, hence is either one or minus one; this
selects the parity. Splitting a unit according to its sign gives the formula on
all real units.

`realCharacterData` selects those proved parameters and packages them in the
published `RealCharacterData` structure. Its character field is exactly the
supplied continuous quasicharacter; the formula and the constructor's character
equality are proved.

The only inputs are the actual continuous characters and the previously derived
covering-lift helpers. The complex additive normalization uses the published
field-trace character, with no change to its scale convention. Complex
multiplicative character presentations, transport to infinite completions,
existence of nontrivial local restrictions, and the global analytic conclusions
remain separate obligations.
