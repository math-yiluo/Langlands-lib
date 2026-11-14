# Reduction of KP 2.2.16 through the adjoint quotient

This internal helper module proves a reduction of the exact
`BoundedOpenNormalizerStatement`; the two new boundedness inputs remain
explicit hypotheses.

`hasDenseRationalPointFamily_subgroup_of_isOpen` proves that an analytically
open subgroup of the rational points of a smooth connected affine group
over a nonarchimedean local field is Zariski dense as an actual
rational-point family. Smoothness and connectedness give integrality.
The published `rationalLocalDensity` theorem applies to the nonempty open
subgroup, using its identity element for nonemptiness. The image of that
open set in the scheme is contained in the union of the images of the
subgroup's actual rational points, which is therefore dense.

`boundedOpenNormalizer_of_adjoint_inputs` assumes
`DenseBoundedNormalizerAdjointStatement` and
`AdjointNormKernelBoundedPreimageStatement`, at the same arbitrary universe.
For the connected reductive group in KP 2.2.16, the published
`adjointQuotientExistence` theorem constructs an actual quotient `q : G → A`
by the full scheme center. The open subgroup is dense by the first helper.
The first assumed input bounds the image of its normalizer in `A(F)`.
The second assumed input bounds the preimage of that image after
intersection with the actual rational common norm kernel. The requested
normalizer intersection is a subset, so monotonicity of algebraic
boundedness concludes the exact target.

All point topologies are the canonical rational-point topologies.
No building data or additional condition on the open subgroup enters
the reduction. It does not prove either boundedness input and does not
assert an unconditional proof of KP 2.2.16.

The provenance is internal composition of the named Library results.
The target is KP Proposition 2.2.16, Kaletha–Prasad, *Bruhat–Tits theory: a
new approach* (2023), printed pp. 77–78, PDF pp. 108–109, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The implemented reduction is a different route from the source's use of
Lemma 2.2.15.
