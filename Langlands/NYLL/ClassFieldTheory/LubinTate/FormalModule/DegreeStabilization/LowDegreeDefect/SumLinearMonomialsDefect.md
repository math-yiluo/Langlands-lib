# M351.028: the defect of a finite linear sum vanishes through degree one

`Langlands.NYLL.PortInternal.M351.d028` proves the exact published proposition
`Langlands.NYLL.PortInternal.M351.d028Statement e ebar L s q hq`.
For `H = ∑ i ∈ s, monomial (single i 1) (L i)` and `q.degree ≤ 1`, it asserts
that the coefficient of `q` in `defect e ebar H` is zero. Here the defect is
`PowerSeries.subst H e.toPowerSeries - MvPowerSeries.subst (fun i ↦ inVariable ebar i) H`.

The theorem retains the independent universes `u v w` and exactly the binders
`{K : Type u} [Field K] {F : LocalField.{u, v} K} {π : F.valuationSubring}
{σ : Type w} [Finite σ] (e ebar : LubinTateSeries F π)
(L : σ → F.valuationSubring) (s : Finset σ) (q : σ →₀ ℕ)
(hq : q.degree ≤ 1)`. It introduces no `Fintype σ` instance or uniformizer
hypothesis. The finite set `s` is arbitrary, including the empty set.

## Source and attribution

The target is source unit M351.028 of Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The source has `omit [Fintype σ] in` at line 841 and the private theorem
`LubinTate.SameUniformizer.coeff_defect_sum_linear_monomials_eq_zero`
at lines 842–888. Its file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The original is readable below
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The original copyright, Apache-2.0 and author header is retained in Lean,
followed by Worker 519's dated modification record. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply and are unchanged.
No patch10 edit affects this source module; no applicable NYLL erratum was
found in the published errata filenames.

## Implemented proof

The proof computes both sides of the defect directly in degrees at most one.
It does not use the source's induction on `s` or the general monomial response
M351.025.

The private helper `coeff_subst_low_for_linear_sum` shows that, for any
multivariate series `H` with zero constant coefficient,

```text
coeff q (PowerSeries.subst H e.toPowerSeries) = π * coeff q H
```

when `q.degree ≤ 1`. `PowerSeries.coeff_subst` expands the left side as a
finite-support sum over natural exponents. The exponent-zero term vanishes
because `e.constantCoeff_eq_zero`. For an exponent `n` other than zero or one,
`q.degree < n`. Mathlib's `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero`
puts the order of `H ^ n` at least `n`, so `MvPowerSeries.coeff_of_lt_order`
makes its coefficient zero. `finsum_eq_single` leaves only exponent one;
`e.coeff_one_eq_uniformizer` identifies its coefficient as `π`.
This helper needs no finite-variable assumption.

In `d028`, the local equality `hmono` writes each linear monomial as
`L i • MvPowerSeries.X i`, using linearity of `monomial`. The local fact
`hconstant` proves that the finite sum has zero constant coefficient:
map the constant-coefficient homomorphism through the sum, then use
`coeff_monomial_ne` because `single i 1 ≠ 0`. This is the elementary fact
appearing in source M351.021 (lines 604–611), proved directly without
creating a second public theorem.

The helper therefore evaluates the coefficient of the left substitution
as `π * coeff q H`. For the right substitution, the published theorem
`inVariable_hasSubst ebar` supplies the substitution algebra homomorphism.
Mapping it through the finite sum and scalar multiples sends `X i` to
`inVariable ebar i = PowerSeries.subst (X i) ebar.toPowerSeries`.
The same helper, now with `H = X i`, evaluates this coefficient as
`π * coeff q (X i)`. Linearity of coefficients and commutativity of
multiplication identify the two finite sums; `ring` closes each scalar
identity. Subtracting their equal coefficients gives zero.
Only the zero constant and common linear coefficient fields of the two
Lubin–Tate series are used; their residue Frobenius fields are not needed.

## Imports and dependencies

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.Statements`,
  providing the unchanged exact target and shared definitions;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst`,
  providing the published proof of the finite-family substitution condition;
- `Mathlib.RingTheory.MvPowerSeries.Order`, providing the power-order and
  coefficient-vanishing lemmas.

The substitution definitions and coefficient formulas are available through
those imports. The remaining steps use Mathlib's linear maps, algebra
homomorphisms, finite sums, `finsum_eq_single`, `omega`, `exact_mod_cast` and
`ring`. The proof imports no M351.021 or M351.025 proof, no sibling low-degree
proof, and no external NYLL source module. The only top-level helper is
private under a fresh name; no new public prerequisite is introduced.

## Adaptations

Extract the exact source signature to the prescribed focused proof module,
prefix it with `Langlands.NYLL`, and give the source-private theorem its
reserved port name `PortInternal.M351.d028`. State its type using the
published `d028Statement`. Retain `[Finite σ]` from the source's omission of
`[Fintype σ]`; use `classical` only within the main proof.

Replace the original induction and M351.025 application by the direct
coefficient argument above, and prove the needed M351.021 fact locally.
The source's substitution condition M348.003 is reused by its published
Lean name. Replace the original broad imports by the three focused imports
listed above. The source's ambient classical decidability and
`noncomputable section` are unnecessary for the private helper; the main
proof explicitly introduces classical reasoning. Replace the module
exposition with this proof-specific documentation and retain attribution
with a dated notice. No published target or imported file is modified.

## Development validation

The proof was compiled without warnings or errors through the project Lean
service in approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
This development check is separate from independent semantic review and
publication.
