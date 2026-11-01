# Generation opens for a fixed line bundle on a quasi-affine scheme

This internal development proves that the generation opens of global sections of
one fixed actual line bundle form an open basis on a quasi-affine scheme. No
positive tensor power of that line bundle is used in the result.

First, a global section generates wherever its coordinate in a rank-one chart
is a unit. The proof tests the section morphism on all smaller opens: the
coordinate map identifies it with multiplication by a unit, which is bijective.

If a global principal open D(f) lies inside a bundle chart, take the local frame
with coordinate one. The principal-open extension theorem produces a global
section whose coordinate on D(f) is a nonnegative power of f, hence a unit.
Tensor that section with f as a section of the trivial line bundle and transport
through the left unitor to the original bundle. The published tensor-section
generation-locus formula shows that the resulting generation open is exactly
D(f). Finally the affine global principal opens of a quasi-affine scheme form
a basis, so they can be chosen inside a chart and any prescribed neighborhood.

The provenance is derived infrastructure: the coordinate maps come from the
published LineBundleSectionClearingProof, the extension step from
LineBundlePrincipalSectionExtension, the generation-locus and isomorphism
transport formulas from the published Library, and the quasi-affine principal
basis from Mathlib. Compactness and quasi-separatedness in the extension step
are supplied by quasi-affineness. The argument applies in arbitrary universe.

The public definition `QuasiAffineSectionBasis.sectionOnBasicOpen` chooses such
a global section and includes its exact generation-open equality as a subtype
certificate. It uses `exists_section_basicOpen` by noncomputable choice. The
companion theorem `isBasis` is the basis conclusion used in finite avoidance.
