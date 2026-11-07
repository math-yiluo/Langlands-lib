# Equal norm classes when the local norm subgroup is top

The sole new declaration is the closed proposition definition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOfLocalNormSubgroupEqTopStatement.{u} : Prop`.
It asserts that if the actual local norm subgroup is the top subgroup,
the canonical norm classes of any two base-field units coincide.
This module defines the assertion; its truth proof is deferred.

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U040.Proofs`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Full telescope and mathematical meaning

There are no external term or instance parameters. The definition's body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
  (h : localNormSubgroup K L = ⊤) (x y : Kˣ),
  normClass K L x = normClass K L y
```

All eight binders are internal and preserve their source order and kinds:

| Position | Binder | Kind and role |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure on `K` |
| 4 | `[Field L]` | Instance-implicit field structure on `L` |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `(h : localNormSubgroup K L = ⊤)` | Explicit named subgroup-equality hypothesis |
| 7 | `(x : Kˣ)` | Explicit first base-field representative |
| 8 | `(y : Kˣ)` | Explicit second base-field representative |

The sole universe parameter `u` is arbitrary and shared by `K` and `L`.
The hypothesis `h` is an equality in `Subgroup Kˣ`. Its left side is
the actual image of the unit norm `normUnits K L : Lˣ →* Kˣ`; its
right side is the top subgroup, containing every base-field unit.
The representatives `x` and `y` are arbitrary units of `K`, explicitly
quantified after `h`. The conclusion equates their canonical projections
in `NormQuotient K L`.

The name `h` is retained even though the conclusion does not depend on
its proof term. As in the public U029, U036 and U040 statements,
`linter.unusedVariables` is disabled only for this definition.
The hypothesis remains syntactically `localNormSubgroup K L = ⊤`.
There is no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise.

The inherited constructions retain their concrete meanings:

| Declaration | Meaning and public module |
| --- | --- |
| `normUnits K L` | `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, from `LocalField.NormUnits.U002.Definitions` |
| `localNormSubgroup K L` | The image `(normUnits K L).range`, from `NormQuotient.U001.Definitions` |
| `NormQuotient K L` | `Kˣ ⧸ localNormSubgroup K L`, from `NormQuotient.U002.Definitions` |
| `normClass K L` | The canonical homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`, from `NormQuotient.U005.Definitions` |

Here `LocalField` abbreviates the module prefix
`Langlands.NYLL.ValuedFieldTheory.LocalField`, and `NormQuotient` in
the module column abbreviates its `NonarchimedeanLocalField.NormQuotient`
branch. U003.Definitions supplies the quotient commutative group
structure. The general algebra norm convention is inherited without
restriction. The host `Langlands.LocalClassField.NormQuotient`, whose
signature includes finite-dimensionality, remains a separate interface.

## Relation to the published assertions

The imported chain contains `NormClassEqIffDivMemStatement.{u}` in
U019.Statements and its exact theorem `normClass_eq_iff_div_mem` in
U019.Proofs. Its body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔ x / y ∈ localNormSubgroup K L
```

This criterion expresses equality through membership of `x / y` in
the actual norm image. The pinned original M093.041 proof uses its
reverse implication, rewrites membership using `h`, and applies
`Subgroup.mem_top (x / y)`. This describes the source proof route.
The present module supplies only the proposition definition.

The public U040 assertion
`NormClassEqAllOfNormUnitsSurjectiveStatement.{u}` has the same
conclusion and representative order, but its named hypothesis is
`h : Function.Surjective (normUnits K L)`. Its proof
`normClass_eq_all_of_normUnits_surjective` is already public in
U040.Proofs. The new U041 assertion preserves the original subgroup
equality hypothesis. This contribution proves neither the U041 assertion
nor an equivalence between these two hypotheses. The exact proof child
for `Langlands.NYLL.LocalFieldTheory.normClass_eq_of_localNormSubgroup_eq_top`
follows independent publication of this statement.

## Pinned original and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:372–378`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L372-L378).
Line 372 is the retained docstring; 373 introduces
`normClass_eq_of_localNormSubgroup_eq_top` and `K L`; 374 supplies
the three instances, the named hypothesis `h` and explicit `x y`;
375 is the conclusion; and 376–378 are the deferred original proof.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

The original subgroup, quotient, group structure and projection appear
at lines 26–54 of the same file. The actual unit norm appears at
lines 32–34 of `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`,
whose whole-file SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1766 read the original header and these NormQuotient passages,
the complete NormUnits source, and recomputed both hashes on
6 November 2026 UTC.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_of_localNormSubgroup_eq_top` | Closed `NormClassEqOfLocalNormSubgroupEqTopStatement.{u}` in this module |
| Proof `normClass_eq_of_localNormSubgroup_eq_top` | Deferred exact proof with the adapted source name |
| `normClass_eq_iff_div_mem` | Existing public U019.Proofs theorem, inherited through U040.Proofs |
| `normClass_eq_all_of_normUnits_surjective` | Existing public U040.Proofs theorem for the surjectivity form |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with their original meanings |

The adaptation prefixes the namespace and packages the complete asserted
type in a named closed Prop-valued definition, preserving the shared
universe, all eight binders and the conclusion. The sole U040.Proofs
import replaces the original import list. The original truth proof,
noncomputable section, unused universe `v` and unrelated declarations
are omitted. No instance or simp registration is added.
The [public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places M093.041 after M093.040.END and makes its completion the final
M093 scheduling boundary. No patch10 edit applies to M093.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths under `notes/errata/` were checked in the
workspace, project and supplied Library on 6 November 2026 UTC;
all six paths were absent.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 1766's dated modification
record. Worker 1766 authored this extraction and companion from the
pinned original and published dependencies. No unpublished project draft
is reused, and there are no project coauthors.

The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, remain unchanged in `repository_paths`.
Their respective SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the retained originals.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Compilation and declaration
inspection are development evidence. Independent semantic acceptance
and integration are required for publication under `lean.statement@1`.

Only the statement phase of M093.041 is covered. Its truth proof and
host adapters remain separate work. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the named Artin family,
actual norm image and exact norm kernel, host quotient evaluation and
bijectivity, actual quotient topology, finite discrete Galois topology
and both continuity directions for every prime and arbitrary supplied
`TF` and `TE`. Type 0 remains an intermediate host stage.
Normalization, inertia, universe transport, cohomological comparison and
reciprocity proofs remain separate obligations. Existing cohomological
definitions and frozen proof targets retain their meanings.
