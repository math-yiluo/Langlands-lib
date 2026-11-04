# Proof of the Hausdorff criterion from the actual affine-line origin

The theorem `affineSchemeHausdorffCriterion` proves exactly
`AffineSchemeHausdorffCriterion R S`. Its hypotheses are arbitrary commutative
rings R and S in the common scheme universe, an R-algebra structure on S, and
a topology making S a topological ring. No topology on R is needed. The
statement is the separately submitted actual-scheme formulation of the
paragraph after Proposition 2.1 on printed page 2 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The sufficiency direction uses the closed-embedding conclusion of that
proposition through its existing actual-affine-scheme proof.

`isClosed_range_affineLineOrigin_iff` works with any topology family T
normalized on the actual affine line. It installs the assigned topology on
that line's S-point space. The coordinate evaluation equivalence is then a
homeomorphism by the normalization hypothesis. The existing exact algebraic
range law identifies the image of the actual origin with the inverse image
of the singleton zero. A homeomorphism preserves closedness in both
directions. Mathlib's
`IsTopologicalAddGroup.t2Space_iff_zero_closed` identifies closedness of this
singleton with Hausdorffness of S, whose additive group is topological by the
explicit topological-ring hypothesis.

`t2Space_of_affineSchemeTopologyClosedEmbeddings` applies the strengthened
closed-embedding property to the actual morphism Spec R → Spec R[t]
given by zero evaluation. The existing origin construction supplies its
closed-immersion instance. Both schemes are affine of finite type over R.
The resulting closed embedding has closed range, so the first theorem gives
Hausdorffness.

The final theorem assembles these two results for the first two clauses of
the target. For the canonical global-section evaluation family, the existing
`affineLinePointHomeomorph` supplies line normalization, so necessity follows.
Conversely, Hausdorffness is installed as an instance and the published
`isClosedEmbedding_affineSchemePointMap` proves the required property for
each actual finite-type affine closed immersion. All spaces retain their
independently constructed evaluation topologies.

The proof follows Conrad's origin and topological-group argument. It uses
only line normalization for necessity because continuity of the additive
operations is explicit in the hypotheses. It permits the zero ring and
nonfaithful algebra structures. It adds no locality, open-unit,
local-compactness or finite-presentation premise.
