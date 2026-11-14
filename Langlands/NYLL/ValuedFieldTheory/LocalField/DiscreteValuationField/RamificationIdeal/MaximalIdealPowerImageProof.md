# M344.003: maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex

The theorem `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex` proves exactly the published target
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndexStatement` from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.ImageStatements`. It does not edit the statement or its imports.

The source result is `maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex` in
`LocalFieldTheory.DiscreteValuationField.ValuedExtension`, from
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationIdeal.lean`,
lines 77–88, at NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The target's paired Markdown gives the complete source statement correspondence.

The four universes remain independent. The complete common telescope is:

```lean
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
[base.valuation.HasExtension target.valuation]
```

The remaining source binders are exactly `(n : ℕ)`.
No finite-dimensionality or additional module hypothesis is introduced.
The chosen `CompleteDVF` projections, valuation subrings, maximal ideals and
canonical algebra from `Valuation.HasExtension` are the published ones.
The source M108.003 index and M108.005 map are used via their exact Mathlib bodies,
`Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` and
`algebraMap base.valuationSubring target.valuationSubring`.

The proof first unfolds the target statement by `change` to its exact body.
Write `f` for `algebraMap base.valuationSubring target.valuationSubring`,
`m` for `base.maximalIdeal`, `M` for `target.maximalIdeal` and `e` for
`Ideal.ramificationIdx' m M`. It then rewrites in three steps:

1. `Ideal.map_pow` turns `Ideal.map f (m ^ n)` into `(Ideal.map f m) ^ n`.
2. The published M344.002 theorem
   `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex`,
   imported from
   `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.MaximalIdealImageProof`
   and applied to the same `base` and `target`, replaces `Ideal.map f m` by
   `M ^ e`, giving `(M ^ e) ^ n`.
3. `pow_mul` rewrites the right side `M ^ (e * n)` as `(M ^ e) ^ n`, and the
   goal closes by reflexivity.

This is the source's three-step `calc` proof (lines 81–88), with the
canonical Mathlib map and index bodies in place of the source wrappers. The
exponent remains `e * n`, in that order. The only imported results are
the published target and M344.002 modules; `Ideal.map_pow` and `pow_mul` come
from the pinned Mathlib.

The modifications are the `Langlands.NYLL` namespace prefix, the explicit
published `Statement` result type, focused imports, the two canonical wrapper
substitutions, and the replacement of the source's `calc` block by the
equivalent `change`/`rw` chain described above.
The original Apache-2.0 copyright and author header is retained, with Worker 308's
modification record; Worker 308 supplied the proof design and Worker 429 prepared
this pair for submission. The carried [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
