# The vanishing of `Ĥ_cʳ(G_S, M)` in degrees `≥ 4`: statement

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingStatement.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω`, and `Ĥ_cʳ(G_S, M) = compactCohomology ι M r` the cohomology
with compact support with respect to the places of `S`, modified at the real places by Tate's cohomology.

`TateCompactSupportVanishingStatement`: for a finite smooth `G_S`-module `M` killed by an `n ≠ 0` such that
every finite place above `n` lies in `S`, `Ĥ_cʳ(G_S, M) = 0` for every `r ≥ 4`. It is proved in
`Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof` (`tateCompactSupportVanishingStatement`).
Equivalently (the finite local terms vanishing in degrees `≥ 3`), the localization
`Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is surjective for `r ≥ 3` and injective for `r ≥ 4`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.TateCompactSupportVanishingStatement.{u} : Prop
```

## Outline of the proofs

A definition.

## Declarations

`TateCompactSupportVanishingStatement`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10) (long exact sequence of Poitou–Tate; (ii): `Hⁱ(G_S, A) ≅ ⊕_{𝔭 real} Hⁱ(k_𝔭, A)` for `i ≥ 3`), statement p. 489, proof of (ii) pp. 490–491 (degree `3` from the duality of the class formation (8.4.4) and (7.2.17); the degrees `i ≥ 3` by the exact sequence `0 → A → Ind A → B → 0` and induction).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 ((c): `Hʳ(G_S, M) ≅ ∏_{v real} Hʳ(K_v, M)` for `r ≥ 3`); proof pp. 60–61 (p. 61: the exact sequence ending in `H³(G_S, M) → ⊕_{v real} H³(G_v, M) → 0` and the isomorphisms for `r ≥ 4`, from the class formation).
