# Structural finiteness recovered from a represented algebraic space

This internal comparison uses the existing diagonal and atlas predicates
unchanged. It supplies actual scheme finiteness for a scheme representing a
space, which is needed before applying scheme model existence.

`schemeDiagonalArrowIso` identifies the left map of the diagonal into the
product in `Over S` with the actual scheme diagonal of the structure map.
The codomain comparison is `Over.prodLeftIsoPullback`; the domain is unchanged.
Both projection equations follow from the universal properties of the products.

`isQuasiSeparated_schemeToSpace_iff` is valid over every scheme base.
In the reverse comparison to the published implication, it applies the
space's quasi-compact diagonal predicate to the identity chart twice.
The pullback of the two identity maps is the identity square.
The chart pairing is the slice diagonal, so the arrow comparison transfers
quasi-compactness to the scheme diagonal. This is precisely quasi-separatedness
of the structure map.

`finitePresentationAtlas_schemeToSpace_iff` assumes an affine base.
The published LFP compatibility recovers LFP of the structure morphism.
A quasi-compact atlas scheme is compact over the affine base; the actual
surjective atlas map to the represented scheme makes that scheme compact.
A morphism from a compact scheme to the affine base is quasi-compact.
Conversely, LFP and QC of the structure map give the identity atlas with both
properties on the same actual scheme.

`schemeFiniteness_of_presheafIso` combines these comparisons with whole-presheaf
isomorphism transport. It recovers LFP, QC and quasi-separatedness of the actual
structure morphism from the unchanged quasi-separatedness and LFP/QC-atlas
conditions on the space, over an affine base.

All results are derived from the published chart-pairing criterion, represented
atlas recovery, scheme diagonal, compactness, and isomorphism transport. No
limit descent or representability existence assertion is assumed or proved here.
