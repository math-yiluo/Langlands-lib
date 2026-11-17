# Actual Whittaker bounds in supplied orbit seminorms

`cuspWhittaker_smoothBound_of_bandBound` takes the actual finite-level
`CuspidalWhittakerBandBound`, a supplied representation π by bounded complex
operators on a normed complex space E with a group model I, a complex linear
map j from the original cuspidal operator space into E, and a map ζ from
the actual real Lie algebra into the model vector space.

Two comparison hypotheses are explicit. First, the norm of j(v) must equal
the actual determinant-band quotient Haar L² norm for every original v.
Second, j must send the actual real-generator action on every original
vector to the corresponding orbit derivative for π. No alternate positive
form or arbitrary L² measure replaces the band norm in these hypotheses.

For each fixed compact open finite-adelic subgroup J and compact adelic set
Q, the theorem provides a finite family of model Lie words and a
nonnegative real constant. They bound the actual Whittaker coefficient on
Q for every J-fixed original vector, by the sum of iterated orbit-derivative
norms of j(v). The subgroup and compact set precede the family and constant;
the original vector and group point follow them.

The proof takes the actual enveloping derivative bound, applies
`sum_norm_enveloping_le_iteratedLieDerivatives` with the genuine enveloping
action of the operator realization, rewrites the band norms by the supplied
norm identity, and multiplies the two nonnegative constants. This is an
internal derived consequence of the actual band bound and the algebraic
real-word comparison.

This establishes the finite seminorm estimate on the image of the original
J-fixed vectors. It does not construct π or j, prove smoothness or density
of that image, or extend the coefficient functional to all smooth Hilbert
vectors. In particular, it does not assert
`IsContinuousOnSmoothVectors` for a functional on the full smooth-vector
space. The hypotheses allow a general normed E and do not assume or supply
a Hilbert globalization or uniqueness theorem. If the band bound is obtained
from `OperatorCompactSobolevStatement`, that Sobolev premise remains open.
