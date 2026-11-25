# Duality of the Tate–Shafarevich groups of `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/ShaProof.lean`, namespace `Langlands.GaloisCohomology`.

This file proves `PoitouTateShaStatement`, with no hypothesis: for a finite smooth `G_S`-module `M`
killed by `N`, with the places above `N` in `S`, `Ш¹(G_S, M)` and `Ш²(G_S, M')` are finite and the
pairing `Ш¹(G_S, M) × Ш²(G_S, M') → ℚ/ℤ` is perfect. As `PoitouTateDualityStatement` in
`DualityProof.lean`: `PoitouTate.isShaDuality_of_hypotheses` applied to
`PoitouTate.tatePoitouTateHypotheses` for `N ≠ 1`, the zero module for `N = 1`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.poitouTateShaStatement.{u} : Langlands.GaloisCohomology.PoitouTateShaStatement
```

## Outline of the proofs

For `N ≠ 1`, `PoitouTate.isShaDuality_of_hypotheses` (`Assembly.lean`) applied to `PoitouTate.tatePoitouTateHypotheses ι S N hS hN` (`Reduction.lean`); for `N = 1` the module is zero (`PoitouTate.isShaDuality_of_subsingleton`).

## Declarations

- `poitouTateShaStatement` (theorem): **Duality of the Tate–Shafarevich groups of `G_S`**, for every finite smooth `G_S`-module killed by `N`, with the places above `N` in `S`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
