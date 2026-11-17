# Finite real-word bounds for actual enveloping derivatives

This internal algebraic and norm estimate uses the published
`enveloping_real_left_induction`. It introduces `realEnvelopingWord`, the
ordered product of the genuine enveloping generators of a list of actual
real Lie directions. The empty word is the unit; cons is left multiplication
by the corresponding real generator.

`mem_span_realEnvelopingWord` proves that these words span the actual complex
enveloping algebra. The proof uses the published induction principle;
submodule span induction verifies closure under left multiplication by a
real generator, using cons of the word. No choice of basis or PBW independence
result is required.

For any complex algebra action on an algebraic complex vector space V and any
complex linear map j into a normed complex space,
`norm_enveloping_le_realWords` bounds the norm of j applied to one enveloping
derivative by a constant times finitely many real-word derivative norms.
The proof chooses a finite linear combination of words and uses the sum of
the coefficient norms as a common bound on each coefficient.
`sum_norm_enveloping_le_realWords` handles a finite family of enveloping
operators, taking unions of the word sets and sums of their constants.
All constants are nonnegative and are chosen before the vector.

The result is algebraic: it needs neither a topology on V, a group
representation on the normed space, nor differential compatibility of j.
It supplies one step toward comparing actual determinant-band derivatives
with iterated Lie derivatives in a supplied smooth Hilbert globalization.
It establishes no globalization, compatibility identity, density, extension
of functionals, or uniqueness of Whittaker functionals.
