# Conditional étale comparisons from actual field isomorphisms

Worker 634.

Assume the unchanged AffineSplitIsomorphismTheoremStatement. Let M be a
supplied affine pinned model and H another reductive group over its base.
Suppose the actual pullbacks of M.group and H are isomorphic at every supplied
algebraically closed field-valued point. Then above each base point there is an
affine étale chart carrying an actual group isomorphism between their
pullbacks. AffineComparisonChart stores these maps and isomorphisms;
AffineComparisonAtlas chooses a point-indexed family covering the base.

The proof takes a pinned étale chart of H through the point, and scalar-extends
M to its actual ring. At an algebraic closure of the chart point's residue
field, the supplied field isomorphism and the chart identification give an
isomorphism of the two pinned groups' field fibres. The published intrinsic
root-datum comparison yields an equivalence of their full constant integral
root data. The assumed affine split isomorphism theorem then gives the actual
group isomorphism over the entire chart ring. Composing with the two actual
chart identifications gives the result.

This is an internal conditional reduction. It does not assert the affine split
isomorphism theorem and does not infer equality of morphisms from their field
fibres. The classification and étale-local reduction are the route used in
Conrad, *Reductive group schemes* (2014), Proposition 6.4.4, pp.232–233; the
invoked affine split theorem is Theorem 6.1.17, p.197.
