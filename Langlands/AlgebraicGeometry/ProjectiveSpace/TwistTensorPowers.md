# The projective twists as tensor powers

For any commutative ring `A` and nonnegative integers `m, d`,
`exists_twistTensorPowIso A m d` constructs an isomorphism from the actual
right-associated tensor power of `twistOne A m` to the fraction sheaf
`(twistLineBundle A m d).obj`. It carries the pure tensor power of each
coordinate section `Xⱼ` to the homogeneous section `Xⱼ^d / 1`. The
noncomputable definition `twistTensorPowIso` chooses this witness.

The proof first identifies the restriction of a product section with the
image of the restricted pure tensor under the sheafification unit.
Bilinearity and induction then show that a local coefficient relation
`s = r • t` becomes the relation with coefficient `r^d` on `d`-th
powers. For `d > 0`, the sections `Xⱼ^d / 1` and the powers of `Xⱼ` both
generate on `D₊(Xⱼ)`. On a chart `D₊(Xᵢ)`, their relative coefficients are
both `(Xⱼ / Xᵢ)^d`: for the fraction sheaf this is computed in the
homogeneous localization, and for tensor powers it follows from the local
coefficient result. The published matching-sections theorem therefore
glues the comparison. For `d = 0` all of the coordinate powers are the
unit and the section `1 / 1` gives the global trivialization.

This is an internal comparison of the Library's existing fraction twist
and explicit sheafified tensor product; neither sheaf is replaced. It
makes no assertion about base-change coherence or about general global
sections of the twists being represented by homogeneous forms.
