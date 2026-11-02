# Support-preserving coefficients of base-changed sections

This internal derived module constructs
`restrictionScalarSectionsBaseChangeMap`, the canonical scalar comparison on
sections of a pulled-back module along the restriction map, followed by the
published pullback-square isomorphism. It applies to any commuting square
`gZ ≫ i = i' ≫ g` and any compatible change of affine base rings. The word
"restriction" does not impose a closed-immersion hypothesis.

`scalarSectionsBaseChangeMap_comp_restriction` proves that extending the
downstairs section-restriction map and then applying this comparison agrees
with scalar comparison on the whole scheme followed by upstairs restriction.
On one-tensor generators, the proof uses the actual adjunction-unit section
maps and the published `unit_comp_pushforwardSquareIso_eq` identity. The
pushforward-square comparison acts identically on top sections, which removes
the extra transport, by `pushforwardSquareIso_hom_app_top_general`. The suffix
distinguishes this arbitrary-square lemma from the affine-base specialization in
`AffineDirectImageBaseChange`. This commutation result assumes no cohomology comparison.

Over a field extension, `exists_vanishing_coefficient_generating` takes a
specified actual line bundle `M` and an upstairs section of its actual pullback.
It assumes that the two canonical scalar global-section maps, on `M` over `X`
and on `i* M` over `Z`, are isomorphisms. If the section vanishes after actual
pullback along `i'` and generates at a point `y`, the conclusion supplies an
actual downstairs section of the same `M`, vanishing after pullback along `i`
and generating at `g y`.

The proof lifts the upstairs section through the first canonical isomorphism.
Commutation and injectivity of the transported second comparison put its lift
in the scalar extension of the downstairs restriction kernel. The
`ScalarExtensionKernels` coefficient-selection lemma detects a kernel section
by the linear observation given by actual pullback to the residue-field
spectrum at `y`. The published line-bundle residue criterion makes this
observation nonzero. The published whole-generation-open pullback equality
then gives generation at `g y`. Thus support and generation are preserved
together. All fields and schemes lie in arbitrary universe `u`; no separability,
finiteness, reducedness or separatedness is assumed here.

This is an internal consequence of the imported actual pullback, scalar
extension, residue and adjunction constructions. It does not establish the
two scalar comparison isomorphisms, compactness, affineness, or the complete
ampleness-reflection theorem.
