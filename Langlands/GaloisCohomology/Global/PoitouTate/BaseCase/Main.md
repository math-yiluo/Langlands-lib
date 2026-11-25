# The base case of Poitou–Tate duality

`Langlands/GaloisCohomology/Global/PoitouTate/BaseCase/Main.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

For a number field `K` containing the `n`-th roots of unity, `n` a prime power, `n` odd or `K` totally
complex, and `S` finite containing the places above `n`, the abstract base case
(`BaseDualityHypotheses` of `Langlands.GaloisCohomology.CompactSupport.BaseCase`) applies to `G_S`
with `D = μ_n`, the local traces `localTrace` and the trace `finiteTrace`. All its hypotheses
except the perfectness of the pairing `H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n` (cup product followed by
`finiteTrace`) are proved in the files this one imports; the perfectness, which is the class field
theory of `G_S` in this degree, is the statement `RootsOfUnityPairingStatement`, and
`rootsOfUnityDualityStatement_of_pairing` proves `RootsOfUnityDualityStatement` from it. The
statement is proved in `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Pairing`
(`rootsOfUnityPairingStatement`, which imports this file), and
`Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Proof` applies the two.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.RootsOfUnityPairingStatement.{u} : Prop
Langlands.GaloisCohomology.PoitouTate.rootsOfUnityDualityStatement_of_pairing.{u}
  (hpair : Langlands.GaloisCohomology.PoitouTate.RootsOfUnityPairingStatement) :
  Langlands.GaloisCohomology.PoitouTate.RootsOfUnityDualityStatement
```

## Outline of the proofs

Each field of `BaseDualityHypotheses` is a theorem of this directory (`dualizingModule_ρ_apply_of_mem`, `bijective_localTrace_cupPairing`, `bijective_finiteTrace`, `finiteTrace_ptLocalToCompact`, the vanishing and finiteness lemmas, `compactCupRes_zmodMulPairingRight_swap`), except `ker_left` and `ker_right`, which are `RootsOfUnityPairingStatement`; then `BaseDualityHypotheses.bijective_compactZmodDualityMap`.

## Declarations

`RootsOfUnityPairingStatement`, `rootsOfUnityDualityStatement_of_pairing`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
