# A line-bundle section generating at finitely many points of a quasi-affine scheme

`Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleFiniteSectionStatement.{u}`
asserts that, for every quasi-affine scheme `X`, every actual Library line bundle
`L`, and every finite subset `E` of `X`, there is a global section `s` of `L.obj`
whose whole generation open contains `E`.

Here `LineBundle X` is an actual module sheaf locally isomorphic to the structure
module. `GlobalSections L.obj` is its module of sections on the whole scheme.
`trivializationOpen L.obj s` is the union of all opens on which the actual map
`sectionHom L.obj s : O_X ⟶ L.obj` is an isomorphism. Thus the conclusion asks
that this section generate the rank-one module near every point of `E`.
The published `lineBundle_stalkFrame_set_eq` and
`lineBundleResidueOpenComparison` identify this open with the stalk-frame set
and the nonzero residue-value set, respectively; this statement does not
import or assume either comparison as a hypothesis.

There is no Noetherian, reducedness, integrality, connectedness, or field
hypothesis. The empty finite set and the empty scheme are included.
Mathlib's quasi-affineness convention includes quasi-compactness. The section
belongs to `L` itself, without replacing it by a positive tensor power.

The source is Stacks Project Lemma 28.30.7, tag
[0F20](https://stacks.math.columbia.edu/tag/0F20), specialized to `W = X` and
with its additional affineness conclusion omitted. The source proves the
result for every finite `E ⊆ W` with `W` open and obtains a section with
`E ⊆ X_s ⊆ W` and `X_s` affine. This module retains only the finite-point
generation consequence. It is a proposition definition and supplies no proof
or new axiom.

The retained original is `0F20.html` in the registered source
`stacks-section-open-prerequisites-2026-10-29`, directory SHA256
`290fd705ee87e9b334a225352ff3b4d9118789a923dac35712126f59581269cf`,
at `literature/Stacks Project — Section-open lifting and finite avoidance (HTML snapshot 2026-10-29)`.
The complete statement, proof and empty comments section were read; the live
tag was also checked on 1 November 2026 and agrees with the retained text.
No corresponding project errata note was found in the bounded current
Library, project and private note searches.

This isolates a global-generation prerequisite for constructing regular
sections on Noetherian quasi-affine schemes. The separate task concerning
embeddings of line bundles into the structure module also needs a finite
associated-prime test and an actual dual-evaluation map. Neither of those
conclusions is asserted here.
