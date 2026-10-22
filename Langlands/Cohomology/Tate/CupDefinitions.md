# Tate cup product by dimension shifting

Author: Worker 45.

This file constructs a bilinear family on Mathlib's actual Tate cohomology.
Its initial value in degrees `(0,0)` is the previously constructed quotient
of the invariant tensor pairing by the actual norm images. The first
degree is extended in both directions using the actual connecting
isomorphisms of the scalar-split coefficient shifts and their tensor
sequences. The second degree is then extended in the same manner, with
the factor `(-1)^p` at each second-factor boundary. This sign is represented
by the integer value of `Int.negOnePow p`.

Every connecting isomorphism used in this recursion has already been
constructed from a proved short exact sequence and proved vanishing of
its coinduced middle coefficient. Tensor exactness follows from the
explicit scalar splittings. No flatness assumption is imposed by this
construction.

An equivariant bilinear coefficient pairing is converted to an actual
equivariant map from the tensor representation. Applying the actual Tate
cohomology functor to that map gives the corresponding pairing-valued
family. In particular, scalar multiplication supplies `integralH2Cup`,
whose first input is ordinary second group cohomology, transported through
Mathlib's comparison, and whose second input is Tate cohomology of the
actual trivial module over `ULift.{u} Z`. The output degree is `n + 2`,
with the explicit degree transport from the tensor family's `2 + n`.
The group and all coefficient carriers retain the arbitrary universe `u`.

This file contains the construction only. Its laws (degree-zero
normalization, coefficient naturality, the boundary formulas for arbitrary
short exact sequences, restriction compatibility and the projection formula)
are stated and proved separately; none of them is an input here.

Source: Serre, *Local Fields*, Greenberg translation, GTM 67, Springer
(1979), Chapter VIII, section 3, Proposition 5, printed pp. 131–132
(PDF pp. 137–138). The first boundary has no sign and the second boundary
has sign `(-1)^p`. The explicit recursive implementation is an internal
dimension-shifting construction; Serre's proof of existence by a complete
resolution is not being assumed. For the integral second input used in
local Tate reciprocity, see Chapter IX, section 8, Theorem 14, printed
p. 149 (PDF p. 155); no arithmetic statement from that theorem is claimed.
Source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
