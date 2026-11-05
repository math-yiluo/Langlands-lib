# Equal norm classes from left multiplication by a unit norm

The sole new declaration is the closed proposition definition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOfEqNormUnitsMulStatement.{u} : Prop`.
It states that if one base-field unit equals an extension-unit norm times
another base-field unit, their canonical norm classes are equal. This module
defines the assertion; it does not prove its truth.

Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U035.Proofs`.
That published Lean/Markdown pair and its full imported chain remain unchanged.

## Full telescope and mathematical meaning

The definition has no external term or instance parameters. Its body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] {x y : Kˣ} (z : Lˣ)
  (h : x = normUnits K L z * y), normClass K L x = normClass K L y
```

All nine binders are internal and retain their original order and kinds:

| Position | Binder | Kind and role |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure on `K` |
| 4 | `[Field L]` | Instance-implicit field structure on `L` |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `{x : Kˣ}` | Implicit first base-field representative |
| 7 | `{y : Kˣ}` | Implicit second base-field representative |
| 8 | `(z : Lˣ)` | Explicit extension-field unit |
| 9 | `(h : x = normUnits K L z * y)` | Explicit named equality hypothesis |

The shared universe `u` is arbitrary. The implicit representatives `x` and `y`
are still universally quantified; neither is a chosen witness. The hypothesis
`h` is an equality in the unit group `Kˣ`. Its right side has `normUnits K L z`
as the left factor and `y` as the right factor. This product is formed before
projection. The conclusion equates `normClass K L x` and `normClass K L y`.
The binder name `h` is retained even though the conclusion does not depend on
the proof term. The unused-variable linter is disabled only for this definition,
following the published U029 statement's convention.

There is no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise. Inherited constructions in
`Langlands.NYLL.LocalFieldTheory` give the exact objects:

| Declaration | Meaning and public module |
| --- | --- |
| `normUnits K L` | `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, from `LocalField.NormUnits.U002.Definitions` |
| `localNormSubgroup K L` | The actual image `(normUnits K L).range`, from `NormQuotient.U001.Definitions` |
| `NormQuotient K L` | `Kˣ ⧸ localNormSubgroup K L`, from `NormQuotient.U002.Definitions` |
| `normClass K L` | The canonical homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`, from `NormQuotient.U005.Definitions` |

Here `LocalField` abbreviates the support prefix
`Langlands.NYLL.ValuedFieldTheory.LocalField`, and `NormQuotient` in the module
column abbreviates its `NonarchimedeanLocalField.NormQuotient` branch.
The quotient commutative group structure is inherited from U003.Definitions.
These public definitions are reused unchanged. The finite-dimensional host
`Langlands.LocalClassField.NormQuotient` is a separate interface.

## Source pin and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:318–325`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L318-L325).
Line 318 opens the equality-refinement section, 320 is the retained docstring,
321 introduces `normClass_eq_of_eq_normUnits_mul` and `K L`, 322 supplies the
three instances, implicit representatives and explicit unit, 323 is the named
hypothesis `h`, 324 is the conclusion, and 325 is the original proof.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

The original norm subgroup, quotient, group structure and projection are at
26–54 of that file. The actual unit norm is at 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1560 read the retained originals and recomputed both whole-file hashes
on 5 November 2026 UTC.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_of_eq_normUnits_mul` | Closed `NormClassEqOfEqNormUnitsMulStatement.{u}` in this module |
| Proof `normClass_eq_of_eq_normUnits_mul` | Deferred exact proof with the adapted source name |
| `normClass_normUnits_mul` | Existing public U032.Proofs theorem, inherited through U035.Proofs |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with the same meanings |

The adaptation adds the namespace prefix, capitalizes the assertion's name
and appends `Statement`, and moves the full original telescope into the body
of a closed Prop-valued definition. It preserves the shared universe and every
binder's order, implicitness and type, including the named left-multiplication
hypothesis. The sole U035.Proofs import replaces the original import list.
The unused universe `v`, noncomputable section, truth proof and unrelated
declarations are omitted. No instance or simp registration is added.
The [public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places M093.036 after M093.035.END. No patch10 edit applies to M093.

The original proof rewrites using `h`, then uses `normClass_normUnits_mul`.
That left-multiplication identity is already public in U032.Proofs and is
available through the unchanged import chain. This records the source route
for a later proof task; this statement pair supplies no proof of the new
proposition. An exact proof task may follow independent statement publication.

The retained source belongs to registration
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths under `notes/errata/` were checked in the workspace,
project and supplied Library on 5 November 2026 UTC; all six paths were absent.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 1560's dated modification
record. Worker 1560 authored this statement extraction and companion directly
from the pinned original, using the published U029 statement for the local
linter convention. No unpublished project draft or patch10 edit was reused,
and there are no project coauthors for this pair.

The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, remain unchanged in `repository_paths`. Their
respective SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Compilation and declaration
inspection provide development evidence. Acceptance and publication under
`lean.statement@1` require independent semantic review and integration.

Only the statement phase of M093.036 is covered. Its truth proof, M093.037
onward and host adapters remain separate work. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the one named Artin family,
actual norm image and exact norm kernel, quotient evaluation and bijectivity,
actual quotient topology, finite discrete Galois topology and both continuity
directions for every prime and arbitrary supplied `TF` and `TE`. Type 0 is an
intermediate host stage. Normalization, inertia, universe transport and the
cohomological comparison still need separate results; this assertion does not
establish them or a reciprocity theorem. Existing cohomological definitions
and frozen proof targets retain their meanings.
