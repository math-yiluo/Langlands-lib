# The vanishing of `Ĥ_cʳ(G_S, M)` in degrees `≥ 4`: proof

`Langlands/GaloisCohomology/Global/RealPlaces/VanishingProof.lean`, namespace `Langlands.GaloisCohomology`.

**Theorem** (`tateCompactSupportVanishingStatement : TateCompactSupportVanishingStatement`). For every
number field `K`, separable closure `Ω`, finite set `S` of finite places, place embeddings `ι`, finite smooth
`G_S`-module `M` killed by `n ≠ 0` with the places above `n` in `S`, and `r ≥ 4`, `Ĥ_cʳ(G_S, M) = 0`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.tateCompactSupportVanishingStatement.{u} :
  Langlands.GaloisCohomology.TateCompactSupportVanishingStatement
```

## Outline of the proofs

By the dévissage `subsingleton_compactCohomology_of_coind` it suffices that `Ĥ_cʳ(G_S, Coind_W(ℤ/2)) = 0`
for every open subgroup `W` when `S` contains the places above `2`, which is
`subsingleton_compactCohomology_coind_zmodRep_two`. The steps, in the modules of
`Langlands.GaloisCohomology.Global.RealPlaces`: `VanishingCriterion` (criterion through the real places,
extensions, retracts), `VanishingDevissage` (odd primes; for `2`, a retract of `Coind_W Res_W M` with `W` of
odd index, filtered by copies of `ℤ/2`), `VanishingUnits` (`H³(G_S, μ₂)` through the `S`-units),
`VanishingTwo` (`ℤ/2` in every degree `≥ 3`), `VanishingPlaces` and `VanishingMackey` (Shapiro and Mackey
at the real places, the fixed field of `W`). The route differs from NSW (8.6.10) and Milne I.4.10, which
use the duality of the class formation of `S`-idèle classes: here the arithmetic input is `H³(G_S, μ₂)`
through the Kummer sequence of the `S`-units and the description of `H²(G_S, 𝒪_Sˣ)` by local classes.

## Declarations

`tateCompactSupportVanishingStatement`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/RealPlaces/Vanishing.lean` (lines 20–37: `gsTateCompactCohomology_eq_zero`, `subsingleton_gsTateCompactCohomology`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Stated as the proof of `TateCompactSupportVanishingStatement` for every universe.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6, (8.6.10) (long exact sequence of Poitou–Tate; (ii): `Hⁱ(G_S, A) ≅ ⊕_{𝔭 real} Hⁱ(k_𝔭, A)` for `i ≥ 3`), statement p. 489, proof of (ii) pp. 490–491 (degree `3` from the duality of the class formation (8.4.4) and (7.2.17); the degrees `i ≥ 3` by the exact sequence `0 → A → Ind A → B → 0` and induction).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 ((c): `Hʳ(G_S, M) ≅ ∏_{v real} Hʳ(K_v, M)` for `r ≥ 3`); proof pp. 60–61 (p. 61: the exact sequence ending in `H³(G_S, M) → ⊕_{v real} H³(G_v, M) → 0` and the isomorphisms for `r ≥ 4`, from the class formation).
