# Polar parameters of actual complex quasicharacters

This internal derived module constructs the published `ComplexCharacterData`
for every actual continuous quasicharacter `η : ℂˣ →ₜ* ℂˣ`. Its character field
is exactly the supplied quasicharacter. No unitarity or preexisting presentation
is required.

`complexExponentialUnit` embeds the positive real exponential into the complex
units. Its value is `exp(x)`, it is continuous, and it carries addition to
multiplication. Pulling `η` back along this map and applying the proved
real-line exponential parameter theorem yields a complex coefficient `c`.
Restricting `η` to `Circle.toUnits` and applying the proved circle-character
theorem yields an integer weight `n`.

For a nonzero complex unit `z`, the proof decomposes `z` into its unit-circle
phase `z/‖z‖` and the positive radial unit `exp(log ‖z‖)`. The homomorphism law
and the two parameter formulas then give
`η(z) = (z/‖z‖)^n * ‖z‖^c`. The definition of the principal complex power on
a positive real base justifies the radial formula. The chosen exponent is
`c/2`, because the unchanged published polar convention uses Euclidean norm
to the power `2*exponent`.

`exists_complexCharacterParameters` proves this normalized polar formula, and
`complexCharacterData` selects the proved weight and exponent by classical
choice. Its character equality is definitional and exposed by a lemma. These
are direct consequences of the earlier covering-lift parameter helpers and
Mathlib's exponential, logarithm and unit-circle identities. No external
classification theorem or global functional equation is assumed. Transport to
actual infinite completions and the global analytic conclusions remain separate
obligations.
