# Balanced scalar normalizations of regular crossing families

This internal unit allows reciprocal scalar normalizations of the explicit
generic crossing families. Such a normalization is needed when a central zero
in one direction accompanies a pole in the other.

A `Normalization` consists of the four removed-denominator choices and a Boolean
specifying an optional division by one parameter. `IsValid` requires validity of
all scalar choices and, when division is selected, the finite-mode `Cancels`
condition. The ambient family is the raw regularization or its simple quotient.
The imported finite-layer derivative construction proves weak analyticity and
finite-dimensional ranges. Composing with the fixed algebraic target retraction
gives a family in the actual target module at every parameter.

On generic nonzero parameters the resulting family is the actual shifted map
multiplied by `z ^ totalOrder / z ^ divisionOrder`. Opposite normalizations are
`Balanced` when the sums of the removed and divided orders agree. Their scalar
product at opposite parameters is then the fixed nonzero scalar of the reverse
normalization at `-1`. Multiplying the reverse family by its inverse gives a
generic left inverse. Weak analyticity, finite-dimensional ranges and a
nontrivial generic filter approaching zero specialize that identity, proving
injectivity at zero.

Scalar multiplication preserves the generic compact intertwining identity.
Specializing this identity proves compact equivariance at zero. This module
retains validity, balance and the generic approaching filter as hypotheses; it
does not construct the arithmetic choices or prove limiting Lie intertwining.
