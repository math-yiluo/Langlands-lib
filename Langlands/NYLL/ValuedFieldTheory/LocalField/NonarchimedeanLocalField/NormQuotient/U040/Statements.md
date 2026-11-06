# Equal norm classes under a surjective unit norm

The sole new declaration is the closed proposition definition
`Langlands.NYLL.LocalFieldTheory.NormClassEqAllOfNormUnitsSurjectiveStatement.{u} : Prop`.
It asserts that surjectivity of the actual norm homomorphism on unit groups
implies equality of the canonical norm classes of any two base-field units.
This module defines the assertion; its truth proof is deferred.

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U039.Proofs`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Full telescope and mathematical meaning

There are no external term or instance parameters. The definition's body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
  (h : Function.Surjective (normUnits K L)) (x y : Kˣ),
  normClass K L x = normClass K L y
```

All eight binders are internal and retain their source order and kinds:

| Position | Binder | Kind and role |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure on `K` |
| 4 | `[Field L]` | Instance-implicit field structure on `L` |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `(h : Function.Surjective (normUnits K L))` | Explicit named surjectivity hypothesis |
| 7 | `(x : Kˣ)` | Explicit first base-field representative |
| 8 | `(y : Kˣ)` | Explicit second base-field representative |

The sole universe parameter `u` is arbitrary and shared by `K` and `L`.
The hypothesis `h` concerns the actual homomorphism
`normUnits K L : Lˣ →* Kˣ`, coerced to a function. It says that each
base-field unit has an extension-field unit as a norm preimage.
The explicit representatives `x` and `y` are arbitrary units, quantified
after `h`; neither is a chosen preimage. The conclusion equates their
canonical projections in `NormQuotient K L`.

The source binder name `h` is preserved even though the conclusion does
not depend on its proof term. Following the public U029 and U036 statement
convention, `linter.unusedVariables` is disabled only for this definition.
The hypothesis remains syntactically `Function.Surjective (normUnits K L)`.
There is no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise.

The unchanged public constructions have the following concrete meanings:

| Declaration | Meaning and public module |
| --- | --- |
| `normUnits K L` | `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, from `LocalField.NormUnits.U002.Definitions` |
| `localNormSubgroup K L` | The actual image `(normUnits K L).range`, from `NormQuotient.U001.Definitions` |
| `NormQuotient K L` | `Kˣ ⧸ localNormSubgroup K L`, from `NormQuotient.U002.Definitions` |
| `normClass K L` | The canonical homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`, from `NormQuotient.U005.Definitions` |

Here `LocalField` abbreviates the support prefix
`Langlands.NYLL.ValuedFieldTheory.LocalField`, and `NormQuotient` in the
module column abbreviates its `NonarchimedeanLocalField.NormQuotient`
branch. U003.Definitions supplies the quotient commutative group structure.
The general algebra norm convention is inherited without restriction.
The host `Langlands.LocalClassField.NormQuotient`, which has a
finite-dimensionality parameter, is a separate interface.

## Relation to the published equality criterion

The imported chain already contains the proposition
`NormClassEqIffDivMemStatement.{u}` in U019.Statements and its exact theorem
`normClass_eq_iff_div_mem` in U019.Proofs. Its body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔ x / y ∈ localNormSubgroup K L
```

This criterion describes equality through membership in the actual norm
image. The original M093.040 proof applies its reverse implication and
uses `MonoidHom.mem_range.mpr (h (x / y))` for the required membership.
The approved Mathlib source
`Mathlib/Algebra/Group/Subgroup/Ker.lean:77–79` states
`MonoidHom.mem_range : y ∈ f.range ↔ ∃ x, f x = y`.
This records the original proof route and the relation between the
assertions. The new module contains only the proposition definition;
it supplies no proof of that proposition. Its exact proof child follows
independent statement publication.

## Pinned original and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:364–370`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L364-L370).
Line 364 is the retained docstring, 365 introduces
`normClass_eq_all_of_normUnits_surjective` and `K L`, 366 supplies the
three instances, 367 gives the named hypothesis `h` followed by explicit
`x y`, 368 is the conclusion, and 369–370 give the deferred original proof.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

The original subgroup, quotient, group structure and projection occur
at 26–54 of the same file. The actual unit norm occurs at 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file
SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1736 read the original header and relevant NormQuotient passages,
the complete NormUnits source, and recomputed both hashes on
6 November 2026 UTC.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_all_of_normUnits_surjective` | Closed `NormClassEqAllOfNormUnitsSurjectiveStatement.{u}` in this module |
| Proof `normClass_eq_all_of_normUnits_surjective` | Deferred exact proof with the adapted source name |
| `normClass_eq_iff_div_mem` | Existing public U019.Proofs theorem, inherited through U039.Proofs |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with their original meanings |

The adaptation prefixes the namespace and moves the complete asserted
type into a named closed Prop-valued definition. It preserves the sole
shared universe, all eight binders and their order, and the conclusion.
The sole U039.Proofs import replaces the original import list.
The original truth proof, noncomputable section, unused universe `v`
and unrelated declarations are omitted. No instance or simp registration
is added. The [public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places M093.040 after M093.039.END. No patch10 edit applies to M093.

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
(assisted by OpenAI Codex)”, followed by Worker 1736's dated modification
record. Worker 1736 authored this statement extraction and companion
directly from the pinned original and published dependencies. No
unpublished project draft is reused, and there are no project coauthors.

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
inspection provide development evidence. Acceptance and publication under
`lean.statement@1` require independent semantic review and integration.

Only the statement phase of M093.040 is covered. Its truth proof,
M093.041 (`normClass_eq_of_localNormSubgroup_eq_top`) and host adapters
remain separate work. Parent task `1cbd1968-d285-4b34-822c-f6b5599d1c38`
retains the named Artin family, actual norm image and exact norm kernel,
host quotient evaluation and bijectivity, actual quotient topology,
finite discrete Galois topology and both continuity directions for every
prime and arbitrary supplied `TF` and `TE`. Type 0 is an intermediate
host stage. Normalization, inertia, universe transport, cohomological
comparison and reciprocity proofs remain separate obligations.
Existing cohomological definitions and frozen proof targets retain
their meanings.
