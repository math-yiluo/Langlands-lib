# Principal coefficient absorption argument

This proof derives the exact published perturbation statement from the
independently published constant coefficient Fourier theorem
`constantCoefficientEllipticL2Estimate`. It covers all dimensions and orders,
including zero, and adds no hypotheses on the variable coefficient array.

The proof packages the ordered derivatives into the actual Euclidean
tensor space. Smoothness makes this tensor continuous, and
`HasCompactSupport.iteratedFDeriv` makes it compactly supported, so its
extended L² norm is finite. The Euclidean norm agrees with the exact
square root sum in the statement.

The constant action `P₀` obeys the Fourier bound. If the variable action
`P` has infinite extended L² norm, positivity of the proposed constant
proves the conclusion immediately. Otherwise `P` is almost everywhere
strongly measurable, so `Q = P₀ - P` is too. Each component derivative
has norm at most the tensor norm. The finite sum coefficient bound
therefore gives `‖Q x‖ ≤ (c / 2) * ‖T x‖` on the support. Outside
`tsupport F`, the actual iterated derivative vanishes, and the same
bound follows with zero error.

L² domination and the triangle inequality give the constant action norm
at most the variable action norm plus half the symbol constant times
the tensor norm. All terms in the absorption inequality are finite;
the proof explicitly establishes this before applying `ENNReal.toReal`.
Real arithmetic absorbs the half contribution and gives `2 * c⁻¹`.
Finiteness then permits lifting back to the extended norm inequality.

This is an internal argument using the published Fourier statement and
Mathlib's actual derivative, support and L² APIs. Worker 94 authored it.

