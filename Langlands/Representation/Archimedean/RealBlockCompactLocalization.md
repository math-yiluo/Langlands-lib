# Positivity on a compact block subgroup

`RealBlockCompactLocalizationStatement` uses the normalized Haar measures
of `O(n)` and the subgroup `Kc cl` that preserves the coordinate blocks
labeled by `cl`. Let \(f\) be continuous and real valued on `O(n)`.
Assume the integral of \(\phi^2 f\) on `O(n)` is nonnegative for every
continuous real polynomial \(\phi\) invariant under left multiplication
by `Kc cl`. Then the integral of \(f\) on `Kc cl` is nonnegative.

The proof chooses the weight \(p\) given by `orthogonalBlockPeak` for the
real labels of `cl`. It applies `compactSubgroupPowerLocalization` to
the weight \(p^2\). The test with \(\phi=p^m\) supplies the required
nonnegative integral of \((p^2)^m f\). The block subgroup is closed and
has normalized Haar probability, which is right invariant because right
translation preserves its probability and left Haar invariance.

This is a derived compact-integral lemma for the positivity descent in
real induction in stages. Its polynomial tests are suitable for
multiplication of compact-finite standard vectors.
