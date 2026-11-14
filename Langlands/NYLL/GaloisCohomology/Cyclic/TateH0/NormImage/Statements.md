# NYLL M095 targets: the unit norm lands in the invariants, finite sums of additive units and the norm subgroup as a kernel

This module extracts three lemma types from Naganori Yamaguchi's
ClassFieldTheory (NYLL), commit `fbd320cd8b1b06487c58227e92eb135794267709`, as
Prop-valued definitions. It supplies targets only and contains no proofs of
them. Proofs are separate `lean.proof@1` work.

## Source

The original is `Nyll/GaloisCohomology/Cyclic/TateH0/NormImage.lean` (206
lines, SHA-256
`a8e71d1ab0523eec0970d399ed9cd92fa5978c7148ff62b075df261c0464feec`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/TateH0/NormImage.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m073-m096.md`, section
M095 (patch status "none in patch10"). The section context is source lines
22–29: `namespace CyclicCohomology`, `open LocalFieldTheory`,
`open CategoryTheory`, `noncomputable section` and `universe u`. The file has
no `variable`, `omit` or `include` command, so each lemma's telescope is
exactly its own binder list.

## Exact source and parameter map

All original names are in `CyclicCohomology`; all target names are in
`Langlands.NYLL.CyclicCohomology`. Append `Statement` to the original name to
obtain the target's exact name. Each target keeps the lemma's binders, in
order and with their binder kinds, as parameters of a definition whose type
is `Prop`. Its body is the lemma's asserted proposition.

| Unit | Original name; docstring / asserted type lines | Paired Lean line | Parameters | Proposition |
| --- | --- | --- | --- | --- |
| M095.002 | `unitsNorm_mem_invariants`; 36 / 37–39 | 36 | `(K L : Type) [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)] (x : Additive Lˣ)` | `unitsNormLinearMap K L x ∈ unitsInvariantSubmodule K L` |
| M095.007 | `additive_toMul_finset_sum_units`; 105 (`@[simp]` 106) / 107–110 | 41 | `{ι : Type*} (L : Type*) [Field L] (s : Finset ι) (f : ι → Additive Lˣ)` | `Additive.toMul (Finset.sum s f) = Finset.prod s (fun i => Additive.toMul (f i))` |
| M095.009 | `additiveNormSubgroup_eq_ker_quotient_map`; 123 / 124–127 | 47 | `(K L : Type u) [Field K] [Field L] [Algebra K L]` | `additiveNormSubgroup K L = (MonoidHom.toAdditive (normClass K L)).ker` |

The universe parameters are as in the source: none for M095.002, two
independent universes (`u_1` for `ι`, `u_2` for `L`) for M095.007 and `u` for
M095.009.

Meaning of the three propositions:

- **M095.002**: for every `x`, the norm `∑_{σ ∈ Gal(L/K)} σ • x` of the unit
  representation is Galois-invariant, i.e. lies in the invariant submodule
  `(Lˣ)^{Gal(L/K)}`. `unitsNormLinearMap` (M095.001) is defined in the sibling
  module `NormImage/Definitions` and `unitsInvariantSubmodule` (M094.001) in
  `TateH0/Invariants/U001/Definitions`.
- **M095.007**: for any field `L`, finite set `s` and family `f` of additive
  units, the unit underlying the sum `∑_{i ∈ s} f i` is the product
  `∏_{i ∈ s} toMul (f i)` in `Lˣ`. Only Mathlib constructions occur.
- **M095.009**: the additive norm subgroup (M095.008, sibling module) equals
  the kernel of the additive form of the canonical projection
  `normClass K L : Kˣ →* Kˣ ⧸ N_{L/K}(Lˣ)`. `normClass` is the published
  M093.005 definition `Langlands.NYLL.LocalFieldTheory.normClass`, reached by
  the source's `open LocalFieldTheory`.

## Modifications (Worker 5454)

- **Extraction**: only the asserted types are taken. Every proof body (source
  lines 40–41, 111–116 and 128–139) is omitted, and so is the `@[simp]`
  attribute of M095.007 (line 106), which has no meaning on a Prop-valued
  definition. The data definitions and the other lemmas of the source file are
  not part of this module.
- **Form**: each source `lemma` becomes a `def … : Prop` with the same
  parameters; the lemma's conclusion becomes the body. Every hypothesis and
  instance argument of the source is kept, in the source order. No parameter
  is unused, so no linter option is needed.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
  `open LocalFieldTheory` now resolves to `Langlands.NYLL.LocalFieldTheory`.
  `noncomputable section` and `universe u` are kept. `open CategoryTheory`
  (line 25) is omitted because no target uses it.
- **Imports**: the sibling data module
  `Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions` (which
  carries the source's Mathlib imports and the M093.001 and M094.001 modules)
  and the published M093.005 module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U005.Definitions`
  for `normClass`. Nothing is redefined here.
- **Docstrings**: the declaration docstrings are the source lemma docstrings.
  The module docstring is a modification notice.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings. Inspection of each target
  reports that it returns `Prop`.
- A private audit module copies each source lemma verbatim, in its source
  section context (`open` commands, `noncomputable section` and universe),
  into the adapted namespace `Langlands.NYLL.CyclicCohomology`, so that the
  source names resolve to the adapted constants, and proves it with the
  verbatim source proof. A `MetaM` command then checks, for each lemma and its target,
  identical universe-parameter lists, identical binder names (after erasing
  hygienic macro scopes) and binder kinds along the parameter telescope, and
  that the lemma's type is definitionally equal to `∀ xs, target xs`. All
  three passed. As a control, a variant of the M115.001 target with its
  parameters `K` and `L` swapped was rejected by the same command.
- A second private module proves each target, applied to its parameters, by
  the verbatim source proof. So the targets are provable in the form stated.
  Those proofs are not part of this contribution.

## Scope

These targets assert elementary facts about the representation norm on units,
finite sums in `Additive Lˣ` and the norm subgroup. They do not assert a
class-formation, cup-product, Tate, transfer or reciprocity result.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
