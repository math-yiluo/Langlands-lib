# The linked positive-inner filtration for two induction blocks

`RealInducedPairPositiveFiltrationStatement` proves the adjacent filtration
for two linked induction blocks of positive absolute weights and positive
signed inner weight. The filtration is on the actual right `O(4)`-finite
standard module, with the permitted pieces and intertwining modulo earlier
ranges of `RealAdjacentFiltration`.

The result is derived from the positive crossed quotient, the kernel
splitting of `RealInducedPairPositiveGenericMiddle`, and the character
lifting theorem of `RealCompactParityLifting`. A section of a vector in
the crossed quotient kernel is taken in the presentation with the first
pair's signs flipped. It splits into two summands whose middle polynomial
images are low along axes 0 and 2, respectively.

For the first summand the lifting theorem flips the signs on axis 0, giving
a vector in the original character presentation. For the second summand
it flips the signs on axis 2, giving a vector in the opposite presentation.
In both cases the lift is low in the middle axis at the signed inner
cutoff. The actual differential tail kills such a vector, and the
tail-kernel theorem expresses it as an image of the inner binomial.

Along the edited outer axis, the lifted primary high coefficients are
those of the input multiplied by their mode sign. Taking double
coefficients preserves this relation because the two outer rotations
commute. The two-tail comparison shows that the quotient maps of the lift
and the input agree. Each of the two summands therefore contributes to the
range of the corresponding parity prefix. Their sum is the original
kernel vector by the section identity.

This establishes the reverse crossed-kernel inclusion used by
`RealInducedPairPositiveTwoPrefix.filtration`. That theorem gives the five
pieces, their intertwining modulo earlier ranges, and the spanning identity.
