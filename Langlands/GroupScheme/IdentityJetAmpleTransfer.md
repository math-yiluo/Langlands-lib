# Actual positive-order identity jets and Lie determinant-dual ampleness

This module completes the transfer from actual identity-jet positivity
to actual Lie determinant-dual positivity, removing the previous explicit
rank-locus base-change premise.

Let `G` be a smooth affine group scheme over a compact quasi-separated scheme
`S`. For a positive integer `n`, the theorem
`IdentityJet.lieDeterminantDual_isAmple_of_positiveJet` assumes that the existing
actual chosen line bundle `IdentityJet.determinant G n` is ample and proves
that the dual of `smoothLieDeterminant G` is ample. These are the determinant
of the actual jet module and the determinant of the actual Lie sheaf,
respectively. There is no global constant-rank, noetherian, splitting or
additional base-change premise.

The definition `openDeterminantBaseChangeIso` first compares the existing
actual chosen jet determinant pulled back along any open immersion with the
existing actual chosen jet determinant of the actual base-changed group.
It composes actual finite locally free determinant pullback with determinant
functoriality applied to `IdentityJet.openBaseChangeIso`. No compactness is
needed for this comparison, and it includes jet order zero.

For the ampleness theorem, choose the actual cotangent finite-frame rank loci.
The previously proved reduction handles each clopen locus using an actual
fixed-index affine cotangent cover. The actual jet-module open-base-change
isomorphism now supplies the required comparison on every rank inclusion.
The rank reduction therefore yields the original actual Lie determinant-dual
ampleness from the original positive-order jet determinant ampleness.

`lieDeterminantDual_isAmple_of_positiveJet_twist` accepts an actual ample line
bundle `M` identified by a supplied actual module-sheaf isomorphism with the
actual positive-order jet determinant tensored with the actual pullback of
any line bundle from an affine base. The affine-base twist ampleness
equivalence removes that factor and the first theorem applies. A
stabilizing complement determinant can enter through this explicit factor;
this module does not assert the required determinant comparison.

The provenance is internal. The implementation combines actual open jet
base change, actual determinant functoriality, the completed clopen rank
reduction and affine-base twist ampleness. It supplies no geometric
positivity of an identity jet and no Grassmannian determinant identification.
Those remain necessary for the finite-parabolic ampleness target.
