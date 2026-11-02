# Proof of the affine DVR integral-point embeddings

This proves exactly `DvrAffinePointProperties R K` from `DvrPointStatements`,
the explicit valuation-topology formulation of Conrad Example 2.3, printed
page 3. It retains arbitrary discrete valuation rings and their actual fraction
fields, without completeness or residue-field assumptions.

The fraction-field injection has the induced topology on its source. Its range
is the closed unit ball of the maximal-ideal valuation: the forward direction
is Mathlib's bound on elements of `R`, and the reverse direction is
`IsDiscreteValuationRing.exists_lift_of_le_one`. The host valuation-topology
theorems show this ball is open and closed, giving both coefficient embeddings.

`affineSchemeChangeRing_eq` identifies actual scheme point change of ring with
coefficient composition between the global-section algebra point spaces.
Published coefficient-map theorems give open and closed embeddings there;
finite type of the coordinate algebra follows from the geometric hypothesis.
The actual-point homeomorphisms transfer both conclusions back to scheme points.
This proof does not address the other examples of Section 2 or nonaffine points.
