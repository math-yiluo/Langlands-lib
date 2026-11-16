# NYLL M351.019: low-degree coefficients of a substituted monomial

The theorem `Langlands.NYLL.PortInternal.M351.d019` proves the published
`Langlands.NYLL.PortInternal.M351.d019Statement`. Write
`O = F.valuationSubring`. For a finite variable type `σ`,
`ebar : LubinTateSeries F π`, exponents `q d : σ →₀ ℕ`,
`hq : q.degree ≤ d.degree`, and `c : O`, it identifies the coefficient of
`X^q` in `c ∏ᵢ ebar(Xᵢ)^(dᵢ)` as
`if q = d then π ^ d.degree * c else 0`.

The complete binder list is
`{K : Type u} [Field K] {F : LocalField.{u, v} K} {π : F.valuationSubring}
{σ : Type w} [Finite σ] (ebar : LubinTateSeries F π)
(q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree) (c : F.valuationSubring)`,
with independent universes `u`, `v`, `w`. There are no additional hypotheses;
in particular `π` need not be a uniformizer, `c` may vanish, and `d` may be
zero. The displayed `if` uses the same local classical decidability instance
as the target and the source.

## Source correspondence

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
Source line 555 is `omit [Fintype σ] in`; the private theorem
`LubinTate.SameUniformizer.coeff_subst_inVariables_monomial_of_degree_le`
occupies lines 556–585, with its proof in lines 564–585.

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its file SHA-256 was checked as
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL errata file was found in the current published notes,
and patch10 makes no change to this source module.

## Implemented proof

Set `A = subst (fun i => inVariable ebar i) (monomial d c)` and
`B = subst (d011 π) (monomial d c)`. The imported theorem `d017 ebar d c`
gives `((d.degree + 1 : ℕ) : ℕ∞) ≤ (A - B).order`.
From `hq`, `Nat.lt_succ_of_le` gives `q.degree < d.degree + 1`;
`exact_mod_cast` transports this strict inequality to `ℕ∞`. Transitivity
places `(q.degree : ℕ∞)` strictly below `(A - B).order`.

`MvPowerSeries.coeff_of_lt_order` therefore gives
`MvPowerSeries.coeff q (A - B) = 0`. Rewriting this equality with
`map_sub` and `sub_eq_zero` identifies the coefficient of `A` with that of
`B`. Rewriting with `d018` gives the required formula for the coefficient
of `B`. This follows the original proof route, including the original
order estimate and coefficient argument.

## Imports and adaptations

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.InVariableStatements`,
  supplying the unchanged target and its shared definitions;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.D017Proof`,
  supplying the order comparison `Langlands.NYLL.PortInternal.M351.d017`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.D018Proof`,
  supplying the linear-model coefficient formula
  `Langlands.NYLL.PortInternal.M351.d018`.

The prerequisite modules supply the shared `d011` linear model and Mathlib's
multivariable power-series order theory transitively. The original whole
`RecursiveCoefficient` and Mathlib `Trunc` imports are replaced by these
focused imports.

The source-private theorem is exposed under its prescribed adapted name
`Langlands.NYLL.PortInternal.M351.d019`, with return type
`d019Statement ebar q d hq c`. The proof begins by unfolding this target
abbreviation. The source-private prerequisite names are replaced by the
imported `d017` and `d018`, and
`linearInVariableStabilization` is replaced by its published port `d011`.
The source namespaces are replaced by `Langlands.NYLL.PortInternal.M351`
and openings of the shared `Langlands.NYLL` namespaces.

The unused source section `[Fintype σ]` is not declared, following its
`omit`; the theorem retains `[Finite σ]`. The unused big-operator scope is
omitted. The universes, binder kinds and order, explicit hypothesis `hq`,
coefficient ring, classical decidability instance and conclusion are
otherwise unchanged. The source copyright, Apache-2.0 release line and
author attribution are retained, followed by a dated modification record.
The original LICENSE and NOTICE are already published under `licenses/NYLL/`.
