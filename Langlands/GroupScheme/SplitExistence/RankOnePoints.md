# Simple rank-one maps on Chevalley rational points

For a simple root \(i\), `ChevGroup.simpleRankOne i` is the Chevalley homomorphism
from \(\mathrm{SL}_2(k)\) to the rational points of the represented Chevalley
group. The upper and lower unipotent matrices go to the existing root points
of \(i\) and \(-i\) with their original coordinates. The diagonal matrix
\(\operatorname{diag}(a,a^{-1})\) goes to `ChevGroup.corootPt i a`, and the
standard Weyl matrix goes to `ChevGroup.weylPoint i`.

The construction uses the closed embedding into the general linear group.
Transport the entries of an \(\mathrm{SL}_2(k)\) matrix to the global sections
of \(\operatorname{Spec} k\) and apply the simple-root matrix homomorphism
`ChevalleyData.φ`. Its upper and lower transvections are the images of
`rootPt`. These transvections generate \(\mathrm{SL}_2(k)\) over any field, so
the full matrix homomorphism takes values in the range of the injective
rational-point map into the general linear group. Inverting that injection
on its range gives `simpleRankOne`.

The point `corootPt j a` is defined for every root \(j\). Its value on a torus
character \(x\) is \(a^{\langle x,j^\vee\rangle}\).
`corootPt_eq_eval` proves that this is the image in the group of the actual
coroot of `chevDatum k P` evaluated at \(a\). The proof tests the point of the
split torus against each character `charOf k x`. Composing the coroot with
that character is the power map with exponent \(\langle x,j^\vee\rangle\).

The rank-one formulas use Robert Steinberg, *Lectures on Chevalley Groups*,
AMS 2016, Chapter 3, Lemma 19, pp. 22–23, and Chapter 6, relation (C), p. 43.
The literature ID is `steinberg-2016-lectures-chevalley-groups` and the retained
PDF has SHA-256 `e3f9ab93111dd88ff3d944a951f4d39b7e08539f6a9b57f22fba0d9bbc19eb89`.
The passage to the represented group uses the Library's matrix comparisons
for `rootPt`, `torusPt`, and `weylPoint`.
