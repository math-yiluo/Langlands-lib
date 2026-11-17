# Actual determinant sections and affine basis loci

Let `X` be a scheme in any universe, `M` an actual sheaf of modules, and
`T i` an open covering equipped with actual free sheaf charts of the same finite
rank `k`. The covering index type is arbitrary; `k` may be zero. This internal
construction uses the published finite locally free determinant defined by
its actual transition matrices.

A tuple `s : Fin k → Γ(M, ⊤)` gives, in each local basis, the determinant
of its coordinate matrix (`determinantCoefficient`). Restriction commutes with
these determinants (`determinantCoefficient_restrict`), and change of basis
multiplies them by the determinant transition function
(`unit_mul_determinantCoefficient`). The resulting compatible family therefore
defines a global section `determinantSection` of the actual determinant line
`VariableDeterminantFrames.lineBundle e hT`.

`inf_trivializationOpen_determinantSection` identifies the intersection of the
section's generation open with each chart as the basic open of its coordinate
determinant. If these basic opens are `T i ⊓ U` for every chart, then
`trivializationOpen_determinantSection` identifies the whole generation open
with `U`.

For compact `X`, suppose a family of affine opens `U a` covers `X`, and each
`U a` is presented by these basic-open equations for some tuple `s a` of
global sections. Then `isAmple_of_affine_basisLoci` proves ampleness of this
determinant line. No affineness of the frame charts is required.
`finiteLocallyFreeDeterminant_isAmple_of_affine_basisLoci` transports that
conclusion to `finiteLocallyFreeDeterminant hM` for any finite local basis
witness `hM`.

The implemented proof uses the actual section bases supplied by free sheaf
charts, the multiplication identity for coordinate matrices, and the published
cocycle gluing construction. The criterion follows by using the determinant
sections in the first tensor power, through `tensorRightUnitor`, and the
definition of `LineBundle.IsAmple`. The comparison with the standard determinant
uses `finiteLocallyFreeDeterminantPresentationIso` and invariance of ampleness
under module sheaf isomorphism.

This construction is derived from the existing determinant and cocycle APIs;
it asserts no parabolic ampleness result. In particular, producing global
tuples, the affine covering opens and their basic-open equations remains a
hypothesis of the criterion. Constant rank is a hypothesis of this auxiliary
construction, not an added hypothesis on the parabolic target.
