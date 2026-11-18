# Bounds on bounded-`H₀` subsets of the full minimal Levi

This internal helper isolates the topological bounded-region step used in
Waldspurger (2003), Lemma VI.2.3, printed p.301. It uses the actual minimal
Levi and the already defined `rationalMinimalH0`. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The statements are internal interfaces derived from the current Library.

`HasMinimalLeviCompactSublevels` asserts that, for each real `R`, all minimal-Levi
points with `N(H₀(m)) ≤ R` are contained in some compact subset of the full
minimal Levi. It asserts compact containment rather than closedness or
compactness of the sublevel set itself.

The height comparison of `RationalMinimalLeviHeight` puts this set inside a
matrix-height ball for a supplied closed matrix embedding. That ball is compact
in the actual ambient rational-point topology. The actual minimal Levi is a
closed subgroup, so the ball's preimage in it is compact. This argument does
not require continuity of `H₀`. The supplied matrix embedding is of finite size `Fin n` with `Nonempty (Fin n)`.
The height-comparison lemma requires no extra geometric premises beyond its
explicit comparison and closed embedding. The Cartan-covering corollary derives the height
comparison from the existing compactness and empty-index standard-Levi covering.

`HasMinimalLeviCompactSublevels.exists_norm_le_weight` takes a jointly continuous complex function family indexed by a
compact topological space, and a continuous everywhere-positive real weight.
The norm divided by the weight is bounded on the product of the parameter
space and the compact containing set. This gives a single positive constant
bounding the whole family by that weight on the bounded-`H₀` region.

Continuity, positivity and compactness of the actual analytic family are
explicit premises of this topological lemma and are not proved here. It does
not supply actual orbit-family realization or the full positive-part decay
theorem.
