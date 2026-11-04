# Convolution families induced by actual automorphic actions

This internal adapter starts with an actual automorphic action on the
spectrum of a commutative Hopf algebra whose group-like elements span.
For a parameter algebra `R` over the field and an `R`-valued point `s`
of the acting group, it constructs `convolutionFamily`.

For every coefficient `R`-algebra `A`, the construction identifies
convolution points of `R ⊗ C` with actual points of `Spec C` on
`Spec A`, applies the action of the pullback of `s`, and transports back.
Naturality follows from naturality of the actual action and both
point identifications. This is a genuine
`Langlands.ConvolutionFamily.EndFamily`, so its classifying map is a
coalgebra endomorphism by the preceding algebraic construction.

The field, parameter algebra and test algebras lie in one arbitrary
universe. No reducedness or smoothness of the target is required.
Action triviality and the geometric centre consequence are not yet
asserted by this adapter.
