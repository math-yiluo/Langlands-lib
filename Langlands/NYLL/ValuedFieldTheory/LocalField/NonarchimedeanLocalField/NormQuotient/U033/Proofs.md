# Right multiplication by a unit norm

This module proves
`Langlands.NYLL.LocalFieldTheory.normClass_mul_normUnits.{u}` with exact
unapplied type
`Langlands.NYLL.LocalFieldTheory.NormClassMulNormUnitsStatement.{u}`.
The target is the independently published closed proposition in
[U033.Statements](Statements.lean). The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U033.Statements`.
Its Lean/Markdown pair and complete imported chain remain unchanged.

## Exact target and mathematical meaning

The proposition unfolds to

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ) (z : Lˣ),
  normClass K L (x * normUnits K L z) = normClass K L x
```

There is one arbitrary shared universe `u`. The theorem has no external
term or instance parameter; all seven binders are internal to the target,
in order: `K`, `L`, `[Field K]`, `[Field L]`, `[Algebra K L]`, `(x : Kˣ)`,
and `(z : Lˣ)`. The base unit `x` precedes the extension unit `z`.
There is no finite-dimensionality, finite-module, local-field,
separability, Galois, valuation or topology premise.

The existing `Langlands.NYLL.LocalFieldTheory.normUnits K L` is
`Units.map (Algebra.norm K) : Lˣ →* Kˣ`. Its actual range is
`localNormSubgroup K L`. The existing `NormQuotient K L` is
`Kˣ ⧸ localNormSubgroup K L`, and `normClass K L` is the canonical quotient
homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`. Thus the theorem
says that right multiplication of a representative by a unit norm does
not change its quotient class. The product `x * normUnits K L z` is
formed in `Kˣ` before applying the projection. These constructions and
the quotient commutative-group instance are inherited without edits.

## Implemented proof

The complete proof is

```lean
by
  intro K L _ _ _ x z
  rw [map_mul, mk_normUnits_eq_one]
  exact mul_one (normClass K L x)
```

After introducing the seven internal binders, `map_mul` uses the
homomorphism property of `normClass K L` to give

```lean
normClass K L x * normClass K L (normUnits K L z) = normClass K L x
```

The public theorem
`Langlands.NYLL.LocalFieldTheory.mk_normUnits_eq_one` in U017.Proofs,
inherited through the frozen import chain, replaces the second factor
by `1`. Its mathematical reason is that `normUnits K L z` lies in the
actual range subgroup defining the quotient. Finally,
`mul_one (normClass K L x)` proves the remaining equality. This is the
original proof route verbatim after the added introductions. It needs
neither a new helper declaration nor a new instance or simp registration.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact source passage
is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:295–300`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L295-L300).
Line 295 is the docstring, 296 names the theorem and fields, 297 supplies
the structures and units, 298 is the conclusion, and 299–300 are the proof.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Its original subgroup, quotient, group structure and projection occur
at 26–54, and `mk_normUnits_eq_one` at 171–174.

The associated original
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean` defines the unit norm
at 32–34 and has whole-file SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1560 read both complete retained originals and verified their hashes
on 4 November 2026. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
identifies this as M093.033. No patch10 compatibility edit applies.

| Original declaration or ingredient | Adapted declaration or ingredient |
| --- | --- |
| `LocalFieldTheory.normClass_mul_normUnits` | `Langlands.NYLL.LocalFieldTheory.normClass_mul_normUnits` in this module |
| Original asserted type with its seven binders | Published `Langlands.NYLL.LocalFieldTheory.NormClassMulNormUnitsStatement.{u}` in U033.Statements |
| `LocalFieldTheory.normUnits` | Existing `Langlands.NYLL.LocalFieldTheory.normUnits` in `LocalField.NormUnits.U002.Definitions` |
| `LocalFieldTheory.localNormSubgroup`, `NormQuotient`, `normQuotientCommGroup`, `normClass` | Existing corresponding declarations in `Langlands.NYLL.LocalFieldTheory`, unchanged |
| `LocalFieldTheory.mk_normUnits_eq_one` | Existing `Langlands.NYLL.LocalFieldTheory.mk_normUnits_eq_one` in U017.Proofs |
| Mathlib `map_mul`, `mul_one` | The same Mathlib theorems |

The adaptation adds the namespace prefix `Langlands.NYLL`, replaces the
original import list by the sole public U033.Statements import, and names
the closed published proposition as the theorem type. The original
binders are introduced inside the proof in their original order. The
original docstring and two proof lines are retained. The unused universe
`v`, noncomputable section and all unrelated declarations are omitted.
Worker 1560 adapted this proof directly from the pinned source; no
unpublished project proof draft was reused and there are no project
coauthors.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both sources' `notes/errata/<source id>.md` paths were checked in the
workspace, project and supplied Library; all six were absent on
4 November 2026.

## Scope, attribution and environment

M093.034 onward and the host adapters are separate work. This generic
quotient identity establishes no Artin map, reciprocity, host quotient
topology, continuity, normalization, inertia, universe transport or
cohomological comparison. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains those obligations, with
every prime and arbitrary supplied `TF` and `TE`; Type 0 is an
intermediate host stage.

The Lean file retains the original 2026 Naganori Yamaguchi copyright and
author header verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, and adds a dated modification record. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, remain unchanged in `repository_paths`.
Their respective SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Compilation is development
evidence; independent semantic acceptance and Integrator publication
remain necessary under `lean.proof@1`.
