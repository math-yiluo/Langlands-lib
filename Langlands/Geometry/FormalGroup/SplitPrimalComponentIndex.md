# The first split component of the primal framing

For a split polarized point and its actual square-height special frame and target, `primalComponentIndex` is a locally constant integer on the spectrum of the reduced affine base. It uses the actual integral kernel ranks of the central tensor quasi-isogeny projected to the division summand. The divisibility theorem for special atlas quasi-isogenies supplies the exact division by the reduced division degree \(d\).

`primalComponentIndex_rank` characterizes the index by the relation \(-d n = h\), where \(h\) is the actual central residue-normalized signed height. The sign uses the inverse framing convention in Harris's split component formula. `primalComponentIndex_eq` gives uniqueness for this relation.

`primalComponentIndex_zero_iff` identifies the zero first component on the base with the height-zero certificate on every actual chart. `primalDrinfeldFramedAtlasOfIndexZero` then returns the Drinfeld triple using the projected module, the given residue map, and the actual projected rigidifier.

This is the rank construction for the primal coordinate of Harris (1997), Appendix (A.3), printed p. 114 (PDF p. 40). The underlying special tangent condition and height-zero triple are in Drinfeld (1976), §2A, printed p. 109 (PDF p. 3).
