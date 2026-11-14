# M345.001 proof: additive-valuation restriction

The theorem
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.addVal_integerMap_eq_ramificationIndex_nsmul`
proves exactly the published Library statement
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.addVal_integerMap_eq_ramificationIndex_nsmulStatement`
from the module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal.RestrictionStatements`.
Its result type is that statement applied to `base`, `target` and `a`. It does
not edit the statement or anything the statement imports, and it imports only
the statement module.

## Statement proved

The four universes `u v w x` stay independent. The complete telescope is the
statement's:

```lean
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
[base.valuation.HasExtension target.valuation]
(a : base.valuationSubring)
```

The conclusion is

```lean
IsDiscreteValuationRing.addVal target.valuationSubring
    ((algebraMap base.valuationSubring target.valuationSubring) a) =
  (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal) •
    IsDiscreteValuationRing.addVal base.valuationSubring a
```

The natural number `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal`
acts on `ℕ∞` by natural scalar multiplication. The element `a` ranges over
the whole base valuation subring, including `0`, whose additive valuation is
`⊤`. No finite-dimensionality, module or nonzero-element hypothesis is added.
The valuation subrings, maximal ideals and the algebra map are the published
`CompleteDVF` projections and the canonical algebra structure from
`Valuation.HasExtension`; the statement's paired Markdown records that they
are the exact Mathlib bodies of the source wrappers M108.003
(`ramificationIndex`) and M108.005 (`integerMap`).

## Implemented proof

Write `f` for `algebraMap base.valuationSubring target.valuationSubring` and
`e` for `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal`.
The proof first unfolds the statement wrapper with `change`.

1. **The image of a base uniformizer.** Choose irreducible elements `pi` of
   the base valuation subring and `varpi` of the target valuation subring
   (`IsDiscreteValuationRing.exists_irreducible`). Since `pi ≠ 0` and `f` is
   injective (`Valuation.HasExtension.algebraMap_injective`), `f pi ≠ 0`, so
   `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` writes
   `f pi = u * varpi ^ k` for a unit `u` and a natural number `k`. By
   `IsDiscreteValuationRing.addVal_def`, the target additive valuation of
   `f pi` is `k`.

2. **The ramification index equals `k`.** For every natural number `n`, the
   mapped base maximal ideal lies in the `n`-th power of the target maximal
   ideal exactly when `n ≤ k`. Indeed, the base maximal ideal is the span of
   `pi` (`Irreducible.maximalIdeal_eq`), so its image is the span of `f pi`
   (`Ideal.map_span`); the `n`-th power of the target maximal ideal is the
   span of `varpi ^ n` (`Irreducible.maximalIdeal_eq`,
   `Ideal.span_singleton_pow`). Containment of principal ideals is
   divisibility (`Ideal.span_singleton_le_span_singleton`), which in a
   discrete valuation ring is the order of additive valuations
   (`IsDiscreteValuationRing.addVal_le_iff_dvd`); the additive valuations
   are `n` (`Irreducible.addVal_pow`) and `k`. Taking `n = k` and
   `n = k + 1`, `Ideal.ramificationIdx'_spec` gives `e = k`.

3. **Nonvanishing.** Mathlib provides an `IsLocalHom` instance for the
   valuation-subring algebra map of a valuation extension. If `k = 0`, then
   `f pi = u` would be a unit, so `pi` would be a unit by `isUnit_map_iff`,
   contradicting irreducibility. Hence `k ≠ 0`.

4. **The zero element.** For `a = 0`, both additive valuations are `⊤`
   (`IsDiscreteValuationRing.addVal_zero`), and `k • ⊤ = ⊤` because
   `k ≠ 0` (`nsmul_eq_mul`, `ENat.mul_top`).

5. **Nonzero elements.** For `a ≠ 0`, write `a = unit * pi ^ m`
   (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`), so its base
   additive valuation is `m` (`IsDiscreteValuationRing.addVal_def`). The
   map `f` is multiplicative, the target additive valuation is additive on
   products and scales powers (`addVal_mul`, `addVal_pow`), the image of a
   unit is a unit and hence has additive valuation `0`
   (`IsDiscreteValuationRing.addVal_eq_zero_iff`), and the image of `pi` has
   additive valuation `k`. Therefore the left side is `m • k`, and the right
   side `k • m` agrees after commuting the product in `ℕ∞`.

## Source correspondence and modifications

The source theorem is `addVal_integerMap_eq_ramificationIndex_nsmul` in the
namespace `LocalFieldTheory.DiscreteValuationField.ValuedExtension` of Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationAddVal.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationAddVal.lean#L39-L128),
lines 39–128, at commit `fbd320cd8b1b06487c58227e92eb135794267709`
(file SHA256
`2ea61168d1ded6e730b379aab307057614d161740a64c6dfbfe9b7c0e2f147f6`), from the
registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The statement's paired Markdown gives the complete statement correspondence.

The source proof derives the nonvanishing of `e` and the valuation of the
mapped uniformizer from the maximal-ideal image identity
`m_K · O_L = m_L ^ e` (source M344.002) together with the source inclusion
wrapper `maximalIdeal_map_integerMap_le`. Its handling of the zero element
(step 4) and of nonzero elements through the unit-times-uniformizer-power
decomposition (step 5) is retained. The implemented proof replaces the use of
M344.002 and the inclusion wrapper by steps 1–3: it computes the target
additive valuation `k` of the mapped base uniformizer directly, identifies
`e = k` from the defining property `Ideal.ramificationIdx'_spec` and the
divisibility criterion of the target discrete valuation ring, and obtains
`k ≠ 0` from Mathlib's local-homomorphism instance. The proof therefore does
not depend on the separate M344.002 proof (Task 6247).

The other modifications are the `Langlands.NYLL` namespace prefix, the
published `Statement` result type, the single statement import in place of
the source's two NYLL imports, and the use of the exact Mathlib bodies
`Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` and
`algebraMap base.valuationSubring target.valuationSubring` for the source
wrappers M108.003 and M108.005, as in the published statement.

## Attribution and licence

Worker 308 prepared the proof design in parent Task 5888 and its shared
draft on 13 November 2026, adapting the source proof through M344.002.
Worker 430 replaced the M344.002 route by the direct computation above on
14 November 2026, in Task 6285. The original Apache-2.0 copyright and author
header is retained in the Lean file with both modification records. The
carried [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged (SHA256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
