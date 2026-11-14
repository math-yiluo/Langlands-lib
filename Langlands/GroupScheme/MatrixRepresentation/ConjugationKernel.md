# Full scheme kernel of the dense-span conjugation representation

This is derived infrastructure for the bounded normalizer argument. It uses
`ConjugationSpan`, the published detection of morphisms by dense rational
families, and elementary linear algebra. No separate literature assertion is
introduced.

`ConjugationKernelStatement` concerns a field in arbitrary universe `u`, a
reduced group scheme, a monomorphic finite matrix representation `ρ`, and a
Zariski-dense subgroup `H` of its rational points. For every
`ConjugationSubrepresentation ρ H`, the range functor of the actual scheme
kernel is exactly the full scheme center. The included theorem
`conjugationKernel` proves this statement. Reductivity, finite type and
boundedness are not premises of this result.

The proof first extends a linear projection identity from a specified dense
rational family to every scheme test. It compares two actual maps from the
group to affine coefficient space, then pulls their equality back along
arbitrary points. Consequently, the split inclusion followed by retraction
fixes every point's matrix and inverse-matrix coordinate vector after scalar
extension. Reducedness is used only for this detection on the original group;
no reducedness or affineness is required of the test scheme.

If a point acts trivially on the restricted representation, intertwining shows
that ambient conjugation fixes every column of the inclusion. The projection
identity then implies that it fixes the coordinate values of every point.
Injectivity of coordinate values and monomorphy of `ρ` turn this into
commutativity. Applying the same argument after every pullback gives membership
in the full scheme center, rather than only the center of the rational-point
group.

Conversely, a central point commutes with constant pullbacks of every element
of `H`. The conjugation formula therefore fixes the scalar images of the
generating coordinate vectors. Span induction extends fixedness to the entire
span, including each inclusion column. Intertwining and the split left inverse
give the identity restricted matrix. This converse does not require density,
reducedness or monomorphy. Finally, the existing actual-kernel point equivalence
converts the all-test matrix criterion to equality of subgroup functors.

This pair identifies the kernel. Boundedness of the normalizer's image and the
host bounded-open-normalizer theorem remain subsequent obligations.
