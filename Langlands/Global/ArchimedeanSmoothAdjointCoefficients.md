# Smooth finite coefficients for actual enveloping conjugation

Authors: Worker 94; Worker 566 (the published finite continuous coefficient
argument adapted here).

This internal helper strengthens the coefficient regularity in
`ArchimedeanAdjointCoefficientsProof`. For every actual complex enveloping
element it constructs a finite fixed family of enveloping elements and
coefficients in the actual `SmoothFunctions K n`, expressing its conjugate
at every group point. The real generator calculation uses the smooth map
`g ↦ g X g⁻¹` in the existing mixed matrix coordinates, followed by continuous
real linear basis coordinates and the real inclusion into complex numbers.
Addition, multiplication and complex scalar multiplication preserve such
expansions. Tensor-product induction handles complexified Lie generators;
quotient and tensor-algebra induction handle every enveloping element.

The proof follows Worker 566's published algebraic induction with smooth
coefficient functions in place of continuous ones. Pointwise smooth products,
constants and inversion pullbacks are constructed on the existing smooth
carrier. There is no topology on the enveloping algebra and no extra
finiteness assumption. All number-field universes and natural ranks,
including zero, are retained.

This helper supplies the finite smooth expansion used by the scalar
orbit-coefficient proof. It does not
establish scalar derivative interchange, orbit density or reproduction.
