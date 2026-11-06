# The concrete projective specialization of proper adelic points

`adelicProjectiveComparison` proves the exact
`AdelicProjectiveComparisonStatement` in arbitrary common universe u. The two
component theorems give the curve/function-field and full number-field clauses.
Worker 208 authored the proof and its initial explanation; Worker 1568 verified
and prepared this publication against the accepted Library dependencies.

Each proof installs the actual projective model and canonical generic-fiber
isomorphism from `AdelicProjectiveModels`, retaining their arithmetic adelic
source topology and the independent local product target topology. The existing
properness theorem for polynomial-Proj projective space supplies all finite-type
and properness instances. The proper all-place theorem then proves that the
original coefficient map is a homeomorphism. Proper adelic compactness supplies
CompactSpace on the source. Local scheme-point Hausdorffness gives Hausdorffness
of the full local product, which is transferred back through the proved
homeomorphism. No explicit projective-point coordinates or auxiliary projective
presentation replace the actual scheme-point carriers.

The source is Conrad (2011), printed p.10, Example 4.3, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The implemented route specializes the general proper-scheme comparison and its
valuative/proper-spreading proof instead of repeating the model argument. The
target includes dimension zero as a derived extension of the full-product,
compactness and Hausdorffness claims. The density, diagonal non-discreteness and
affine-line subspace-topology conclusions remain separate parent obligations.
