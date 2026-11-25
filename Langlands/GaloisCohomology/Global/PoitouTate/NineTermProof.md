# The nine-term exact sequence of Poitou–Tate for `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/NineTermProof.lean`, namespace `Langlands.GaloisCohomology`.

This file proves `PoitouTateNineTermStatement`, with no hypothesis: for a finite smooth
`G_S`-module `M` killed by `N`, with the places above `N` in `S`, the sequence
`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M)
→ H⁰(G_S, M')^∨ → 0` is exact, with Tate's `Ĥ⁰` at the real places. As `PoitouTateDualityStatement`
in `DualityProof.lean`: `PoitouTate.isNineTermExact_of_hypotheses` applied to
`PoitouTate.tatePoitouTateHypotheses` for `N ≠ 1`, the zero module for `N = 1`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.poitouTateNineTermStatement.{u} : Langlands.GaloisCohomology.PoitouTateNineTermStatement
```

## Outline of the proofs

For `N ≠ 1`, `PoitouTate.isNineTermExact_of_hypotheses` (`Assembly.lean`) applied to `PoitouTate.tatePoitouTateHypotheses ι S N hS hN` (`Reduction.lean`); for `N = 1` the module is zero (`PoitouTate.isNineTermExact_of_subsingleton`).

## Declarations

- `poitouTateNineTermStatement` (theorem): **The nine-term exact sequence of Poitou–Tate for `G_S`**, for every finite smooth `G_S`-module killed by `N`, with the places above `N` in `S` and Tate's `Ĥ⁰` at the real places.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
