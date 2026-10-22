# Scalar-split Tate dimension shifting

Author: Worker 45.

The positive coefficient shift is the cokernel of the equivariant inclusion
of a representation into the functions coinduced from the trivial subgroup.
The inclusion sends `a` to `g ↦ g a`. Evaluation at the identity is its
scalar-linear retraction. The negative coefficient shift is the kernel of
the augmentation from that same coinduced representation, given by
`f ↦ ∑ g, g⁻¹ f(g)`. The scalar-linear section sends `a` to the function
supported at the identity with value `a`.

Both short exact sequences are actual sequences in Mathlib's representation
category, with short exactness and splitting after forgetting the group
action proved. In particular, the construction does not require the
coefficient module to be flat or projective over the scalar ring.

The two isomorphisms use Mathlib's actual Tate connecting morphisms.
Their invertibility follows from exactness of its Tate long exact sequence
and the all-degree acyclicity proved in `Coinduced`. Thus these constructions
do not assume dimension shifting or vanishing as data.

The mathematical source is Serre, *Local Fields*, Greenberg translation,
GTM 67, Springer (1979), Chapter VII, §1, p. 110 (PDF p. 116), and
Chapter VIII, §1, pp. 128–129 (PDF pp. 134–135). Source ID
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The scalar-ring generality follows the commutative-ring formulation
in the exercise following Serre's induced/coinduced construction.

Both coefficient shifts are functors, using the maps of kernels and
cokernels induced by coefficient morphisms. The connecting isomorphisms
are natural by Mathlib's Tate connecting-map naturality applied to these
actual maps of short exact sequences.

The subgroup operations and cup products built on these shifts are in
`TransferDefinitions` and `CupDefinitions`.
