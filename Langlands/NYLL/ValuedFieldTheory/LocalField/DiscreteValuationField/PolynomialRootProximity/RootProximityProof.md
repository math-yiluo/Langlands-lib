# NYLL M395.002: DVR polynomial root proximity

The paired module proves
`Langlands.NYLL.Polynomial.Splits.exists_root_addVal_eval_le_sub_add_derivative`
with type
`Langlands.NYLL.Polynomial.Splits.exists_root_addVal_eval_le_sub_add_derivativeStatement.{u}`.
It imports the existing target from `PolynomialRootProximity.Statements`
and the multiset comparison proof from
`PolynomialRootProximity.MultisetProductComparison`, both under
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField`.
No definition, statement or imported pair is changed.

## Exact scope

For an arbitrary `R : Type u` with `[CommRing R]`, `[IsDomain R]` and
`[IsDiscreteValuationRing R]`, a polynomial `p : R[X]` satisfying
`p.Splits`, `p.Monic` and `p.natDegree ≠ 0`, and any `x : R`, the theorem gives
`y ∈ p.roots` such that

```text
addVal R (p.eval x) ≤ addVal R (x - y) + addVal R (p.derivative.eval y).
```

The theorem's closed target retains the complete telescope of the published
proposition, with source universe `u`. All comparisons and additions take place
in `ℕ∞`. The proof requires neither distinct roots nor a nonzero derivative;
zero polynomial values, zero differences and infinite valuations are allowed.

## Implemented proof

Splitting identifies the polynomial's natural degree with the cardinality of
its root multiset. The nonzero-degree hypothesis therefore makes `p.roots`
nonempty. `Multiset.exists_max_image` selects `y ∈ p.roots` maximizing
`addVal R (x - y)` over that multiset. This selection works in the linear order
`ℕ∞`, including when the maximum is `⊤`.

For each `z ∈ p.roots.erase y`, maximality gives
`v(x - z) ≤ v(x - y) = v(y - x)`. Applying the additive valuation's
ultrametric inequality to `(y - x) + (x - z) = y - z` then yields
`v(x - z) ≤ v(y - z)`. The published theorem
`Langlands.NYLL.PortInternal.M395.d001` applies to precisely this erased
multiset and these two factor functions. It compares the valuations of the
products of `x - z` and `y - z` over the remaining root occurrences.

`Multiset.cons_erase hy` separates one occurrence of `y` from `p.roots`.
The split monic evaluation formula `hs.eval_eq_prod_roots_of_monic hm`
expresses `p.eval x` as the product over all roots. Valuation multiplicativity
separates its `x - y` factor, and monotonicity of addition applies the product
comparison. Finally, `hs.eval_root_derivative hm hy` identifies the product of
the remaining `y - z` factors with `p.derivative.eval y`.

Erasing one occurrence preserves any additional occurrence of a repeated root,
so the derivative formula and the comparison remain valid in that case. The
proof uses no cancellation or subtraction of valuation values and makes no
finiteness assumption on them.

## Source and adaptations

The proof is adapted from Naganori Yamaguchi's ClassFieldTheory (NYLL), commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PolynomialRootProximity.lean`,
lines 63–145 (theorem and proof). The complete original file was read. It is
retained in the registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Its file SHA-256 is
`fd5707f0f811be973bcba0f0cc9ad3779344dd958da1af8b8647307cc953775d`.
The retained source folder is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026`.

Worker 576 preserved the original maximal-root argument, prefixed the namespace
with `Langlands.NYLL`, and stated the theorem directly at the closed published
proposition before introducing its quantified binders. The original private
helper at lines 34–54 is replaced by the independently supplied public proof
`Langlands.NYLL.PortInternal.M395.d001`; its implementation is not copied into
this module. The original `noncomputable section` is unnecessary for the
proposition proof and is omitted. The target and helper imports replace the
source's direct polynomial and DVR imports; `Mathlib.Data.Finset.Max` is retained
for the maximum-selection lemma. No source hypothesis is added or removed.

The original copyright and author header is retained verbatim. The Library's
[Apache-2.0 LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged. The
modification record in the Lean file identifies Worker 576's adaptations.
