# Levi flats and simple-root projections

`chamberClosure` is the intersection of the closed half-spaces corresponding to the roots positive at its reference point. Each point lies in a closed chamber at a regular reference point. Adding a small positive multiple of a regular vector preserves the signs that are already strict.

The simple roots test membership in the closed chamber by additive generation. At a point of that chamber, every vanishing root belongs to the span of the simple roots that vanish there. A sum of nonnegative evaluations can vanish only when both evaluations vanish. This proves `leviSpaceOf_eq_orthogonal_span_active`.

`simpleRoots_posSet_eq_image` identifies the simple roots of a Levi chamber with the projected nonvanishing simple roots of any ambient chamber whose closure contains its reference point. The kernel of projection is the span of the vanishing simple roots. The other simple roots therefore have independent images. A restricted indecomposable root has a preimage of minimum positive evaluation at the ambient chamber's reference point. Any decomposition of that preimage would either decompose the restricted root or produce a preimage of smaller evaluation. Conversely, every restricted positive root has a nonnegative integral expansion in the projected simple roots. Independence prevents a projected simple root from being a sum of two such roots. `span_projected_positiveSimpleRoots` identifies the span of the images with the orthogonal complement of the center inside the Levi flat.

The roots vanishing at the point are `leviRoots R (posSet R p)`. They form a root set because reflections in them preserve their common orthogonality to the point. The same vanishing roots define `faceSpace R a (posSet R p)` when `p ∈ a` and `a` is a Levi flat.

The root projections implement Arthur's restriction of the complementary simple roots in *An introduction to the trace formula*, §5, printed pp. 25–26. The retained source is `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
