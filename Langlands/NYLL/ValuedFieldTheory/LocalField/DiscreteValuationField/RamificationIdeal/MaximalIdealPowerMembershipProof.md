# M344.004: mapped maximal-ideal power membership (proof)

The theorem
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex`
proves exactly the published statement
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension.integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndexStatement`
of module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.ImageStatements`.
Its result type is that statement applied to `base`, `target` and `hx`.
It does not edit the statement module or anything it imports, and it imports
nothing else.

## Statement proved

Let `K` and `L` be fields with `[Algebra K L]`, and let `base` and `target` be
chosen complete discrete valuation field packages on them, with the base valuation
extending to the target valuation. For every natural number `n` and every element
`x` of the base valuation subring with `x ∈ base.maximalIdeal ^ n`, the image of
`x` under the canonical algebra map
`algebraMap base.valuationSubring target.valuationSubring` lies in
`target.maximalIdeal ^ (e * n)`, where
`e = Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal`.

The complete telescope is the statement's own, with four independent universes:

```lean
{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
(base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
[base.valuation.HasExtension target.valuation]
{n : ℕ} {x : base.valuationSubring} (hx : x ∈ base.maximalIdeal ^ n)
```

No finite-dimensionality, torsion-freeness or other hypothesis is added. The
valuation subrings, maximal ideals and canonical algebra map are the published
`CompleteDVF` projections and the algebra supplied by `Valuation.HasExtension`,
exactly as in the statement.

## Implemented proof

Write `f = algebraMap base.valuationSubring target.valuationSubring`,
`m = base.maximalIdeal`, `M = target.maximalIdeal` and
`e = Ideal.ramificationIdx' m M`.

1. `change` unfolds the statement to its body, `f x ∈ M ^ (e * n)`.
2. The ideal inclusion `Ideal.map f (m ^ n) ≤ M ^ (e * n)` is proved as follows.
   `Ideal.map_pow` rewrites the left side to `(Ideal.map f m) ^ n`, and `pow_mul`
   rewrites the right side to `(M ^ e) ^ n`. Mathlib's
   `Ideal.le_pow_ramificationIdx'` gives `Ideal.map f m ≤ M ^ e`; it holds with
   no hypotheses, because `ramificationIdx'` is defined as the supremum of the
   exponents `k` with `Ideal.map f m ≤ M ^ k`. Raising both sides to the `n`-th
   power with `Ideal.pow_right_mono` closes the inclusion.
3. `Ideal.mem_map_of_mem f hx` gives `f x ∈ Ideal.map f (m ^ n)`, and the
   inclusion from step 2 gives `f x ∈ M ^ (e * n)`.

The kernel check uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source correspondence and change of route

The source result is `integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex`
in `LocalFieldTheory.DiscreteValuationField.ValuedExtension`, in
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationIdeal.lean`,
lines 91–98, at Naganori Yamaguchi's NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The target
statement's paired Markdown gives the full statement correspondence, including
the replacement of the source wrappers `ramificationIndex base.toDVF target.toDVF`
(M108.003) and `integerMap base.toDVF target.toDVF` (M108.005) by their exact
Mathlib bodies `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` and
`algebraMap base.valuationSubring target.valuationSubring`.

The source proof rewrites the target ideal with the equality
`Ideal.map f (m ^ n) = M ^ (e * n)` (source lines 77–88, unit M344.003), which in
turn depends on `Ideal.map f m = M ^ e` (lines 50–73, unit M344.002). It then
applies `Ideal.mem_map_of_mem`. Membership needs only the inclusion `≤`. The
implemented proof therefore replaces the two equalities by Mathlib's unconditional
inclusion `Ideal.le_pow_ramificationIdx'`. The proof does not use the
discrete-valuation structure beyond the objects in the statement, and it does not
depend on the separate M344.002 and M344.003 proof tasks. The final step,
`Ideal.mem_map_of_mem` applied to `hx`, is the same as in the source.

## Modifications and attribution

The adapted file keeps the original Apache-2.0 copyright and author header and adds
a modification record. The carried [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged. The
modifications are: the `Langlands.NYLL` namespace prefix; the published `Statement`
as the result type; a single import of the statement module; the canonical-wrapper
substitutions inherited from the statement; and the proof route above. Worker 308
supplied the initial proof design (through the M344.003 equality). Worker 431
replaced that route with the direct inclusion argument, which needs no upstream
proof module.
