# Actual rank-one two-cell witnesses

This internal derived module packages the exact normalizer representative,
generated-subgroup membership, every-coroot reflection action, and literal
two-cell equality of the published `AffineRankOneTwoCellStatement` into
`AffineRankOneTwoCellData`. Its fields use the original actual affine root
groups, mapped centralizer-zero subgroup, apartment action and affine-root
system, at arbitrary universe.

The chosen jump representative normalizes the mapped centralizer-zero
subgroup. Its supplied opposite pair comes from the imported jump
construction. The imported valuation-functional lemma makes the chosen root
point nonidentity, and the imported reflection normalization theorem then
applies under the apartment axioms and explicit cover-image comparison.
The inverse-conjugation characterization of subgroup normalization supplies
the conjugation input to the imported two-cell assembly.

`affineRankOneTwoCellDataOfBaseSubgroup` constructs the full witness under
the apartment axioms, the explicit
`CoverImageCentralizerNormKernelStatement`, actual
`HasRankOneFactorization`, and a subgroup whose carrier equals the literal
base cell. The subgroup premise remains to be discharged downstream. The
cover-image comparison and actual factor-pair existence also remain
unconditional obligations. This is an intermediate construction, not an
unconditional proof of the published statement. All claims are internal
deductions from the imported constructions and normalization theorem.
