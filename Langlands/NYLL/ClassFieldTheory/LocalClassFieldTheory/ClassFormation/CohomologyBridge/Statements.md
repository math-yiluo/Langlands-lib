# NYLL M114 targets: the unit-representation norm is the Tate norm, and `ρ(g) - 1` is `σ - 1`

This module extracts two theorem types from Naganori Yamaguchi's
ClassFieldTheory (NYLL), commit `fbd320cd8b1b06487c58227e92eb135794267709`, as
Prop-valued definitions. It supplies targets only and contains no proofs of
them. Proofs are separate `lean.proof@1` work.

## Source

The original is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`
(491 lines, SHA-256
`97f7d1f21d8bf5cb2fa787caba600d6820c4be4d91e00d1ebe4f89b89f29830b`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m097-m120.md`, section
M114 (patch status "none in patch10").

The section context is source lines 22–33: `namespace LocalClassFieldTheory`,
`open CyclicCohomology`, `noncomputable section`, `open scoped BigOperators`,
`open CyclicCohomology.ProfiniteCohomology.Herbrand`, `open CategoryTheory`
and the only `variable` command of the file,
`variable (K L : Type) [Field K] [Field L] [Algebra K L]` (line 33). There is
no `omit` or `include` command.

## Exact source and parameter map

Original names are in `LocalClassFieldTheory`; target names are in
`Langlands.NYLL.LocalClassFieldTheory`. Append `Statement` to the original
name to obtain the target's exact name. Each target keeps the theorem's
binders, in order and with their binder kinds, as parameters of a definition
whose type is `Prop`, and its body is the theorem's asserted proposition.
Both theorems mention `K` and `L`, so they include all five section
variables of line 33. The target module keeps the same `variable` command,
which Lean includes in the same way, so each target's full telescope begins
with `(K L : Type) [Field K] [Field L] [Algebra K L]`, as in the source.

| Unit | Original name; docstring / asserted type lines | Paired Lean line | Own parameters after the section variables | Proposition |
| --- | --- | --- | --- | --- |
| M114.001 | `unitsNormLinearMap_toMul_eq_tateNorm`; 35–36 / 37–40 | 42 | `[Fintype (Gal(L/K))] (x : Lˣ)` | `Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) = tateNorm (Gal(L / K)) Lˣ x` |
| M114.017 | `unitsRhoSub_toMul_eq_sigmaMinusOne`; 258–259 / 260–263 | 49 | `(g : Gal(L/K)) (x : Lˣ)` | `(Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g (Additive.ofMul x)) : Lˣ) * x⁻¹ = sigmaMinusOne (Gal(L / K)) Lˣ g x` |

Meaning of the two propositions:

- **M114.001**: for a unit `x` of `L`, the norm of the unit representation
  (`unitsNormLinearMap`, M095.001, which sends `x` to `∑_σ σ • x` in
  `Additive Lˣ`), read back in `Lˣ`, is the multiplicative Tate norm
  `tateNorm (Gal(L/K)) Lˣ x = ∏_σ σ • x` (published M113.001).
- **M114.017**: for `g ∈ Gal(L/K)` and a unit `x`, the unit `g(x) · x⁻¹`
  obtained from the representation action is
  `sigmaMinusOne (Gal(L/K)) Lˣ g x` (published M113.002), the multiplicative
  coboundary `x ↦ (g • x) · x⁻¹`. No finiteness hypothesis occurs.

## Modifications (Worker 5454)

- **Extraction**: only the asserted types are taken. The proofs (source lines
  41–58 and 264) are omitted. The data definitions of the source file are
  either in the sibling module `CohomologyBridge/Definitions` or not part of
  this task.
- **Form**: each source `theorem` becomes a `def … : Prop`, after the same
  `variable` command as the source. Every hypothesis and instance argument of
  the source is kept, in the source order. No parameter is unused in the
  body, so no linter option is needed.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix. The
  source's `open` commands are kept; `CyclicCohomology` and
  `CyclicCohomology.ProfiniteCohomology.Herbrand` now resolve to the
  `Langlands.NYLL` namespaces. `noncomputable section` is kept.
- **Imports**: this port's M095 data module
  `Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions`
  (`unitsNormLinearMap`) and the published M113 data module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions`
  (`tateNorm`, `sigmaMinusOne`), which also carries the source's Mathlib
  import `Mathlib.SetTheory.Cardinal.Finite`. The source's other NYLL imports
  are not used by the statements.
- **Docstrings**: the declaration docstrings are the source theorem
  docstrings. The module docstring is a modification notice.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings. Inspection of each target
  reports that it returns `Prop`.
- A private audit module copies both source theorems with their verbatim
  source proofs, in the source section context of lines 22–33, into an
  auxiliary namespace nested in `Langlands.NYLL.LocalClassFieldTheory`, so
  that the source names resolve to the adapted constants (the proof of
  M114.001 uses M095.007 `additive_toMul_finset_sum_units`, which the audit
  also copies with its source proof). A `MetaM` command then checks, for each
  theorem and its target, identical universe-parameter lists, identical
  binder names (after erasing hygienic macro scopes) and binder kinds along
  the whole telescope, and that the theorem's type is definitionally equal to
  `∀ xs, target xs`. Both passed. As a control, a variant of the M115.001
  target with its parameters `K` and `L` swapped was rejected by the same
  command.
- A second private module proves each target, applied to its parameters, by
  the verbatim source proof. Those proofs are not part of this contribution.

## Scope

These targets compare two descriptions of the norm and of the coboundary on
the units of a field extension. They do not assert a class-formation,
cup-product, Tate, transfer or reciprocity result, or any Herbrand-quotient
comparison.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
