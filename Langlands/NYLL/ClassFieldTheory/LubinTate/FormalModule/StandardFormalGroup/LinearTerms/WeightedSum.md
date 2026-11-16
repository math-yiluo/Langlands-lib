# NYLL M354.003: a weighted sum of linear forms is a linear form

For `L : σ → R` and `M : σ → τ → R`,
`(∑ i, C (L i) * linearForm (M i)) = linearForm (fun j => ∑ i, L i * M i j)`.

## Target and theorem

- Target: `Langlands.NYLL.PortInternal.M354.d003Statement`, published in module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements`.
- Theorem: `Langlands.NYLL.PortInternal.M354.d003` in module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.WeightedSum`, the adapted source name.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`
(SHA-256 `c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`),
lines 76–86 (private theorem `LubinTate.SameUniformizer.HasLinearTerm.linearForm_weighted_sum`). It belongs to registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source/`). The Lean file keeps the
original 2026 copyright, Apache-2.0 and author header and adds a modification
notice by Worker 497; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
apply unchanged.

## Implemented proof

The source proof is reproduced unchanged: extensionality reduces the claim to
coefficients; unfolding `linearForm` and pushing `coeff` through sums and
constant multiples (`map_sum`, `MvPowerSeries.coeff_C_mul`,
`Finset.mul_sum`, `Finset.sum_mul`) gives two double sums over `σ` and `τ`,
which agree after `Finset.sum_comm` and reassociation of the products.

## Adaptations

- Namespace prefix `Langlands.NYLL`; the theorem's type is the published
  target applied to the theorem's parameters, which unfolds (the target being
  a reducible `abbrev`) to the source conclusion.
- The parameters are the source section variables `{R : Type*} [CommRing R]`,
  `{σ : Type w} [Fintype σ]` and `{τ : Type w'} [Fintype τ]`, with the source binders.
- The source theorem is private. As the task prescribes, the port is the
  public theorem `Langlands.NYLL.PortInternal.M354.d003`, whose target is
  `d003Statement`.

- Extract this one theorem from the source's full standard formal-group
  module. Replace its three imports (`RecursiveIntertwiner`, `StandardSeries`
  and `Mathlib.RingTheory.FormalGroup.Basic`) with the single published
  `LinearTerms.Statements` module named above; no external repository is
  imported and no other M354 proof module is needed.
- Omit the source's unused local-field variables `K`, `F`, `π`, the
  `LocalFieldTheory.DiscreteValuationField` open command, and its unused
  universe declarations. Keep the effective ring and finite-variable
  parameters with independent universes, without a field, characteristic,
  nontriviality or nonempty-variable assumption. Omit the unnecessary
  `noncomputable section`; retain or introduce classical decidability only
  at the proof steps that use it. Keep `BigOperators` only where needed.
- Replace the surrounding module and theorem documentation with this focused
  proof documentation. Worker 338 reused Worker 497's shared draft revision 1
  and completed this extraction/adaptation record on 2026-11-16; the draft's
  theorem statement and proof body are unchanged.

The original license files are retained unchanged: `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
The registered source supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching NYLL erratum is present in the Library's `notes/errata/` lookup.
