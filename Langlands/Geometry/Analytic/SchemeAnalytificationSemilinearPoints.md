# Semilinear maps on scheme analytic point spaces

Let \(K\) be a complete nonarchimedean field with nontrivial norm. Take locally finite type structure morphisms \(f\colon X\to\operatorname{Spec}K\) and \(s\colon Y\to\operatorname{Spec}K\), with schemes and field in one universe. An isometric automorphism \(\sigma\) of \(K\) twists \(f\) to \(\operatorname{Spec}(\sigma)\circ f\).

The twist changes the scalar map on each coordinate ring by \(\sigma\). `retwistPoints` therefore carries the same extending seminorms across the affine charts. The chart maps respect restriction and glue. For a scheme arrow \(g\colon X\to Y\) with \(s\circ g=\operatorname{Spec}(\sigma)\circ f\), `semilinearAnalytification` gives the continuous map of glued analytic point spaces by applying ordinary analytification after the retwist. Its chart formula evaluates each target section by pulling it back along the actual scheme arrow.

This uses the affine construction and Zariski gluing of Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields* (1990), Theorem 3.4.1 and Remark 3.4.2, pp. 63–64. The isometric automorphisms give underlying point maps of the kind used for the Galois action in Berkovich, *Étale equivariant sheaves on \(p\)-adic analytic spaces* (1996), §1.1.1(i).

The center of the image is the image of the original center. Ordinary analytification is recovered for the identity field automorphism, and semilinear analytifications compose. The composition proof uses affine neighborhoods subordinate to both scheme maps and the equality of the composite section pullbacks.
