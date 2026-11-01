# Unramified spectral shift of complete pair gamma factors

`UnramifiedTwistGammaStatement.{uF,uV,uW}` states that twisting either member
of a pair by a supplied character `χ` whose value is `|x|^u` transports its
complete symmetric rational gamma certificate by
`G(X) ↦ G(q^(-u) * X)`. The substitution is the published algebra automorphism
`rationalRescale (spectralShiftUnit q hq u)`, including reduced rational
denominators, rather than a pointwise value at a single spectral parameter.

The field and the two carrier universes are independent. The statement keeps
the supplied additive character, self-dual Haar measure, character `χ`, and
both representations. It imposes no irreducibility assumption and asserts
transport of an existing complete certificate. The certificate includes its
functional, nonzero rational witness, and compatible-measure quantifiers.
It does not assert existence of an initial gamma factor or multiplicativity.

This is an internal derived target for the integral spectral-shift argument.
Multiplying one Whittaker coefficient by `|det|^u` shifts the original integral
from `s` to `s+u`; its dual coefficient carries the inverse power and shifts
from `1-s` to `1-s-u`. The unramified character is trivial on determinant signs,
so the central-character sign in the gamma equation is preserved. These two
shifts are the claimed substitution in the scalar gamma factor. The target
extends the existing L-polynomial spectral-shift interface to the complete
gamma relation; no proof is claimed by this proposition definition.
