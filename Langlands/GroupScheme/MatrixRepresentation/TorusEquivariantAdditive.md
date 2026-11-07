# Character shifts for arbitrary torus-equivariant additive actions

This internal derived unit generalizes the coefficient argument in
`Rational.RootActionWeights` from normalized simple-root maps to an arbitrary
supplied homomorphism `x : Ga → G`, a supplied commutative group inclusion
`i : T → G`, and a character `alpha` of either sign.

`VectorGroup.IsTorusEquivariant i x alpha` is the scalar conjugation identity on
every relative scheme test. It asserts neither existence of these data nor that
the image is a root subgroup. The affine conjugation and matrix commutation
lemmas transport precisely this premise to every commutative test algebra.

The coefficient-matrix proof extends a test algebra to its polynomial algebra,
evaluates at the universal additive parameter, and compares coefficients.
The degree-m matrix commutes with the torus matrix with scalar factor
`alpha(t)^m`. When `T` is affine, evaluation at its universal point shows that
the original divided-power coefficient operator sends character space `chi` to
character space `chi + m alpha`. These spaces are the existing all-algebra
character spaces, including tests over nonreduced algebras. The final lemma
expresses the same result in the weight-space notation of a supplied split
pinning.

No field infinitude, positivity of the character, Lie normalization, or
highest-weight representation is assumed. This is a conditional coefficient
calculation, and does not construct root maps or prove Steinberg irreducibility.
The proof route is the existing simple-root coefficient calculation with its
unused simple-root and pinning premises removed; no external source is invoked.
