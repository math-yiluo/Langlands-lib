# NYLL M351.017: monomial substitution and its linear model

This module proves exactly `Langlands.NYLL.PortInternal.M351.d017Statement`
under the name `Langlands.NYLL.PortInternal.M351.d017`. For a finite variable
type, a Lubin–Tate series `ebar` with linear coefficient `π`, an exponent
`d` and scalar `c`, the difference between substituting `ebar(X_i)` and
`π X_i` into `c X^d` has total order at least `d.degree + 1`.

## Source and correspondence

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
SHA-256 `2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
It is registered in `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable entry occurs in the Library's `notes/errata/`.

The source-private theorem is
`LubinTate.SameUniformizer.degree_add_one_le_order_subst_monomial_sub_linear_stabilization`:
line 481 omits the section's `[Fintype σ]` instance, lines 482–490 give the
signature, and lines 491–527 give the proof. The public theorem keeps precisely
`{K : Type u} [Field K] {F : LocalField.{u, v} K}
{π : F.valuationSubring} {σ : Type w} [Finite σ]
(ebar : LubinTateSeries F π) (d : σ →₀ ℕ) (c : F.valuationSubring)` in that order
and with those binder kinds. Universes `u`, `v`, `w` remain independent.
The conclusion is the imported target applied to `ebar`, `d`, `c`.

## Implemented proof

After unfolding the target, the proof applies the private finite-product
estimate to `d.support`, with exponents `d i`. Support membership gives their
nonvanishing. Each inserted series and each linear model has order at least
one, and their difference has order at least two. Unfolding `Finsupp.prod`
and `Finsupp.degree_apply` identifies the resulting bound with `d.degree + 1`.

Both substitutions are then rewritten by `MvPowerSeries.subst_monomial`.
The inserted family admits substitution by the published
`Langlands.NYLL.LubinTate.SameUniformizer.inVariable_hasSubst`; the linear
family admits substitution by the private zero-constant-coefficient argument.
Rewriting the algebra map as `MvPowerSeries.C` and using `ring` expresses
the difference as `c • (P - Q)`. The final bound is the finite-product bound
followed by `MvPowerSeries.le_order_smul`. This includes `d = 0` and `c = 0`.

The missing prerequisites are proved privately under non-conflicting names;
no second public `d010` or `d013`–`d016` is introduced:

| Private helper | Original source unit and lines | Argument |
| --- | --- | --- |
| `order_pow_for_d017` | M351.006, 205–213 | Multiply the order-one lower bound by the exponent and use `le_order_pow`. |
| `order_sum_for_d017` | M351.007, 215–231 | Finset induction and `min_order_le_add`. |
| `order_prod_pow_for_d017` | M351.008, 233–257 | Finset induction, the power bound and `le_order_mul`. |
| `order_pow_sub_for_d017` | M351.009, 259–295 | Factor a difference of powers with the geometric sum; bound each summand and multiply. |
| `order_prod_pow_sub_for_d017` | M351.010, 297–398 | Finset induction; split the difference of products into two terms, each with the required order. |
| `constantCoeff_linear_for_d017` | M351.012, 405–413 | The constant coefficient of `C π * X_i` is zero. |
| `hasSubst_linear_for_d017` | M351.013, 415–421 | Apply `hasSubst_of_constantCoeff_zero`. |
| `one_le_order_inVariable_for_d017` | M351.014, 423–428 | Use the published `constantCoeff_inVariable` and the order-one criterion. |
| `one_le_order_linear_for_d017` | M351.015, 430–435 | Use the private linear constant-coefficient computation and the order-one criterion. |
| `two_le_order_sub_linear_for_d017` | M351.016, 437–479 | Test coefficients of degree below two; split by support in `i` and exponent zero or one. |

These helpers retain the original proofs with only the renamings below.
They are internal to this proof module, justified directly by those source
arguments and Mathlib, without hypotheses standing in for missing proofs.

## Actual imports and adaptations

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.LinearStatements`, supplying the published target and, transitively, the definition `d011 π i = C π * X_i`, `inVariable`, the local-field and Lubin–Tate series definitions, substitution and order;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.ConstantCoeffInVariable`, supplying `constantCoeff_inVariable`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst`, supplying `inVariable_hasSubst`;
- `Mathlib.Algebra.Ring.GeomSum`, supplying `Commute.mul_geom_sum₂`;
- `Mathlib.Tactic.Ring`, supplying the polynomial normalization tactic.

The source's whole `RecursiveCoefficient` and `MvPowerSeries.Trunc` imports
are replaced by these focused modules. Its private linear definition
`linearInVariableStabilization` is the published `d011`; source prerequisite
names are replaced consistently by the private helpers listed above. The source
namespace becomes `Langlands.NYLL.PortInternal.M351`, with the published
`Langlands.NYLL` namespaces opened explicitly. The source theorem becomes
`d017`, with an initial `unfold d017Statement`. The unused section
`[Fintype σ]` is omitted; the actual `[Finite σ]` binder is retained.
`noncomputable section`, `BigOperators`, and the local classical decidability
instance are retained. There is no patch10 edit to this source module.

The original copyright, Apache-2.0 line and author header are preserved,
followed by a dated Worker 224 modification record. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.
