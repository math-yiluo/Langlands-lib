# Xi averaging and chamber weights on an actual standard Levi

The actual standard Levi inherits the compact subgroup used to define the
ambient Xi. `rationalLeviConjugationHalfWeight` is the associated intrinsic
minimal Iwasawa half-weight. On the Levi minimal parabolic its square times
the standard unipotent modulus is exactly the ambient minimal modulus, by
`rationalMinimalModulus_eq_mul`.

The compact envelope of the original matrix height is an invariant
convolution majorant. Restricted to the actual Levi it gives the height in
`ConvolutionWeights`. The construction uses the Levi positivity, continuity,
compact invariance, inversion and normalized compact averaging identities.
Given the lattice Xi upper statement, the inherited simultaneous basis and
finite Cartan cover allow the existing II.1.5 reduction on the representing
Levi scheme. The equivalence with the actual subgroup transports the square
integral with its chosen Haar measure. Monotonicity of square integrability
then permits restriction of the ambient compact envelope as the height.

`rationalLeviXiUpperBound_on_ambientChamber` applies the full-chamber Xi
upper estimate on the representing Levi. Each ambient chamber point is the
image of an actual split torus point. Its defining root inequalities restrict
to the simple roots of the Levi. The closed Levi inclusion identifies the
restricted matrix height, Xi and the Iwasawa weight with their actual subgroup
formulas. This estimate uses the original matrix height on the chamber.

These are derived inputs to the open-cell estimate in Waldspurger VIII.3.1.
The lattice Xi upper statement and the specified Cartan and Iwasawa
factorizations enter through the hypotheses shown in the Lean declarations.
