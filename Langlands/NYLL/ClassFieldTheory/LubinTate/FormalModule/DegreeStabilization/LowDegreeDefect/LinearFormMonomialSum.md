# A linear form is a sum of degree-one monomials

This module proves `Langlands.NYLL.PortInternal.M351.d027`, whose type is the
published proposition `Langlands.NYLL.PortInternal.M351.d027Statement L`.
For every finite variable type `σ` and family `L` of coefficients in the
valuation subring of `F`, it states

```lean
linearForm L =
  ∑ i, MvPowerSeries.monomial (Finsupp.single i 1) (L i)
```

The binders, in order, are `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K}`, `{σ : Type w} [Fintype σ]` and
`(L : σ → F.valuationSubring)`, with universes `u v w`. There is no
uniformizer argument or additional hypothesis.

## Implemented proof

The proof unfolds `d027Statement` and
`Langlands.NYLL.LubinTate.SameUniformizer.linearForm`, whose defining sum is
`∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`.
`Finset.sum_congr rfl` reduces the equality to its summands. For each index
`i`, the proof performs these rewrites:

1. The reverse of `MvPowerSeries.monomial_zero_eq_C_apply` replaces the
   constant series `C (L i)` by the monomial with exponent zero.
2. `MvPowerSeries.X_def` replaces `X i` by the monomial with exponent
   `Finsupp.single i 1` and coefficient one.
3. `MvPowerSeries.monomial_mul_monomial` combines the two monomials by
   adding their exponents and multiplying their coefficients.
4. `zero_add` and `mul_one` give exponent `Finsupp.single i 1` and
   coefficient `L i`, as required.

This is the original source proof with the published proposition unfolded
at its start. It introduces no helper declarations or extra premises.

## Imports and dependencies

The sole direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.Statements`.
That published module provides the target and imports
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions`
and
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`.
These supply `linearForm` and the adapted local-field interface, together
with the Mathlib multivariable power-series operations and identities used
above. The proof uses `Finset.sum_congr` and the five named rewrite
identities; it uses no other NYLL proof theorem.

## Source correspondence and attribution

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
Source unit M351.027 is the private theorem
`LubinTate.SameUniformizer.linearForm_eq_sum_monomial_stabilization`,
lines 829–839: its signature occupies lines 829–833 and its proof
lines 834–839.

The source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright, Apache-2.0 license and author header are preserved,
with a dated modification record. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. Worker 678
prepared this focused proof pair using Worker 495's supplied trial proof.
No patch10 edit affects the source module.

## Adaptations

- Extract this one theorem from the original 943-line module into the
  required `LowDegreeDefect.LinearFormMonomialSum` module.
- Replace the source-private name by the public port-internal name
  `Langlands.NYLL.PortInternal.M351.d027`, following the M351.027 port
  inventory; open the adapted namespaces for the published definitions.
- Express the conclusion as `d027Statement L`, then unfold this abbreviation
  before the original proof. The mathematical equality and the remaining
  tactic steps are unchanged.
- Replace the original `RecursiveCoefficient` and Mathlib `Trunc` imports
  by the focused published statement module. No external source tree is
  imported.
- Retain the source universes and all included binders. Omit its ambient
  `π`, since the source theorem's signature does not use it and Lean does
  not include it in that theorem.
- Omit the ambient `noncomputable section`, `open scoped BigOperators` and
  local `Classical.propDecidable` instance. The finite-sum notation and
  proof elaborate with the published imports and the given `Fintype`
  instance.
- Replace the broad original module exposition with documentation of this
  exact result and its implemented proof.

## Development verification

The focused module and theorem declaration were checked in approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) over Library base
`26a5c21c0dd926a6ba1106b5c4a08f30fdea612c`. Compilation reported zero
errors and zero warnings. Inspection reported a theorem with universe
parameters `u`, `v`, `w` using only `propext`, `Classical.choice` and
`Quot.sound`. This development check does not establish independent
semantic acceptance or publication.
