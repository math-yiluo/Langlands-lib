# Smooth extension of a `(G, M)`-family

`Langlands.GMFamily.smoothExtension` proves `Langlands.GMFamily.SmoothExtensionStatement` from `GMFamiliesStatement`. For a smooth family on the Levi flat of the supplied Euclidean root set, it constructs a smooth function on `StrongDual ℝ a` that agrees with `cM R a c` wherever every chamber denominator `theta a S` is nonzero. The parameter `Λ` represents `iΛ` in the imaginary dual.

## Proof

The restricted simple roots of each chamber are linearly independent by `GMFamilyRootGeometry`. Consequently each normal line occurs at most once in a chamber's denominator. Choose a nonzero representative for every normal line occurring in any chamber, and let `D` be the product of the corresponding imaginary evaluations. Writing each simple root as a real scalar times its line representative expresses its factor as that scalar times the chosen factor. For each chamber, form its contribution to the common numerator by multiplying the family function by the Gram covolume, the inverse product of these scalars, and the factors in `D` missing from the chamber. The sum `N` of these contributions is smooth. Where every `theta` is nonzero, `D` is nonzero and `N = D · cM`.

On a fixed wall away from the other walls, a chamber contribution is zero if its denominator does not include that wall. The other chambers pair with their unique neighbors across the wall. In `GMFamilyWallWeights` the paired covolumes agree and the other denominator factors have equal products on the wall. The family functions agree there by `IsFamily`. The normal roots are negatives of one another and use the same line representative, so their scalars have opposite signs. The two contributions to `N` sum to zero. This proves `N = 0` off the intersections on each wall, and continuity and density within the wall give vanishing at the intersections as well.

`GMFamilySmoothDivision` factors `N` smoothly through `D` by applying the transverse integral formula once per wall. Its quotient is the extension. The final equality follows by cancelling the nonzero `D` on the common nonvanishing locus. Empty products and sums use the usual finite product and sum conventions, so the construction also covers a flat with no walls.

## Source

J. Arthur, *An introduction to the trace formula*, §17, Lemma 17.1 and (17.1), printed p. 94, PDF p. 106. The source uses cancellation of the simple poles from adjacent chambers. The proof implements that cancellation on a common numerator and then uses smooth division on the real dual coordinates. The source is in `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
