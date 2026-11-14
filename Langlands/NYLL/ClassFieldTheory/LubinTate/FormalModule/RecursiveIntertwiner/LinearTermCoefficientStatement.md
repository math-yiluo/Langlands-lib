# NYLL M353.043: low-degree coefficients of an approximation

This pair publishes only the exact proposition target
`Langlands.NYLL.PortInternal.M353.d043Statement`. It does not supply a
proof. Its source is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
private theorem
`LubinTate.SameUniformizer.coeff_eq_linearForm_of_hasLinearTerm`,
M353.043. The signature is at lines 893–899 and the source proof is at
lines 900–905. The source section parameters are at lines 29 and 34–38.
The original file has SHA-256
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.

The readable original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the current `notes/errata/`.

## Meaning and source telescope

For a field `K : Type u`, the shared
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
a variable type `sigma : Type w` with `[Fintype sigma]`, a series `H` over
`F.valuationSubring`, and prescribed linear coefficients `L`, the target
states that `HasLinearTerm H L` implies equality between the coefficients
of `H` and `linearForm L` at every exponent `d` with `d.degree < 2`.
The premise is exactly `HasLinearTerm H L`, which means
`(2 : ℕ∞) ≤ (H - linearForm L).order`.

The three source universes remain independent. The implicit field,
local-field, variable-type, series and linear-coefficient binders and the
field and `Fintype` instances retain their source binder kinds. The
hypothesis `hH`, exponent `d` and strict degree bound `hd` are explicit.
All these binders are universally quantified inside the closed proposition
definition, in source order. The unused source section variable `pi`
does not occur in this theorem's effective telescope. There is no
uniformizer hypothesis or Lubin–Tate-series parameter, and no assumption
about coefficients in degrees at least two.

## Adaptation and dependencies

Worker 325 extracted this signature on 14 November 2026, replaced the source
private name by the agreed public port name, added the `Statement` suffix,
and omitted the proof. No mathematical hypothesis or conclusion was
changed; the local-field specialization is retained.

The target imports the existing shared `LocalField` extending `CompleteDVF`
and the published `linearForm` and `HasLinearTerm` definitions
(M347.001 and M347.003), under `Langlands.NYLL`. Mathlib's
`MvPowerSeries`, `Finsupp.degree` and coefficient maps are reused directly.
The source's `DegreeStabilization` and `RecursiveCorrection` imports are
replaced by these two focused definition modules. This target has no
dependency on recursive-series data, replacement data or predecessor
theorems. Successful focused compilation and declaration inspection verify
this import boundary; publication of the exact proof is a separate task.
No global instances are introduced and no patch10 changes are used.

The original copyright, Apache-2.0 release and author header are retained
verbatim in the Lean file. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are preserved unchanged.
