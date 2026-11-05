# Actual rank-one two-cell data from the two remaining structural inputs

This internal derived module constructs `affineRankOneTwoCellData` at every
actual filtration jump. It retains precisely the apartment axioms, the
explicit `P.zeroDatum.CoverImageCentralizerNormKernelStatement`, actual
`RelativeRoot.HasRankOneFactorization P.i`, the root derivative condition,
and the strict/weak inequality. The imported base-cell subgroup theorem
supplies the subgroup and its exact carrier equality to
`affineRankOneTwoCellDataOfBaseSubgroup`. Thus there is no additional base-cell
or conjugation premise.

The representative is the same actual normalizer point
`affineRankOneReflectionAtJump` chosen in the assembly module. The constructed
data give its membership in the original generated subgroup, its original
apartment action as the affine reflection for every
`AffineRootSystem.IsCoroot P.affineRoots` witness, and the literal equality
with the union of `affineRankOneBaseCell` and `affineRankOneReflectionCell`.
The carrier-equality theorem projects the last field. The existence theorem
projects all four fields to give exactly the existential conclusion of
`AffineRankOneTwoCellStatement` for the supplied field, group, building data,
root and functional.

All objects and the universe scope agree with that published statement.
The cover-image comparison and actual factor-pair existence remain explicit
intermediate inputs and are not proved here. Consequently this module does
not prove the unconditional published statement. Its provenance is internal
composition of the imported base-cell subgroup and actual witness
construction; no new literature assertion or extra mathematical input is
introduced.
