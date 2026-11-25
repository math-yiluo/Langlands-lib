# Poitou–Tate duality for `G_S`

`Langlands/GaloisCohomology/Global/PoitouTate/DualityProof.lean`, namespace `Langlands.GaloisCohomology`.

This file proves `PoitouTateDualityStatement`, with no hypothesis: for a finite smooth `G_S`-module
`M` killed by `N`, with the places above `N` in `S` and `M' = Hom(M, μ_N)`, the duality maps
`Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` (`s ≥ 1`) and `Ĥ_cʳ(G_S, M) → Hˢ(G_S, M')^∨` (`r ≥ 1`) are bijective
for `r + s = 3`. For `N ≠ 1` it is `PoitouTate.isDuality_of_hypotheses` applied to the abstract
hypotheses `PoitouTate.tatePoitouTateHypotheses` of
`Langlands.GaloisCohomology.Global.PoitouTate.Reduction` (which rest on the duality without real
places `PoitouTate.finitePlacesDualityStatement`, the vanishing of `Ĥ_c⁴`
`tateCompactSupportVanishingStatement` and local Tate duality
`PoitouTate.localTateDualityStatement`); for `N = 1` the module is zero.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.poitouTateDualityStatement.{u} : Langlands.GaloisCohomology.PoitouTateDualityStatement
```

## Outline of the proofs

For `N ≠ 1`, `PoitouTate.isDuality_of_hypotheses` (`Assembly.lean`) applied to `PoitouTate.tatePoitouTateHypotheses ι S N hS hN` (`Reduction.lean`); for `N = 1` the module is zero (`PoitouTate.isDuality_of_subsingleton`).

## Declarations

- `poitouTateDualityStatement` (theorem): **Poitou–Tate duality for `G_S`.** For a finite smooth `G_S`-module `M` killed by `N`, with the places above `N` in `S`: `Hʳ(G_S, M) ≅ Ĥ_cˢ(G_S, M')^∨` for `s ≥ 1` and `Ĥ_cʳ(G_S, M) ≅ Hˢ(G_S, M')^∨` for `r ≥ 1`, where `r + s = 3`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
