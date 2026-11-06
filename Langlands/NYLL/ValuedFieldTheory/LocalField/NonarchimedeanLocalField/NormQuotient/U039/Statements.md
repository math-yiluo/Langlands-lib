# Equal norm classes and right multiplication by a unit norm

The sole new declaration is the closed proposition definition
`Langlands.NYLL.LocalFieldTheory.NormClassEqIffExistsNormMulRightStatement.{u} : Prop`.
It asserts that two base-field units have equal canonical norm classes
exactly when the first equals the second times an extension-unit norm.
This module defines the assertion; its truth proof is deferred.

Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U038.Proofs`.
That published pair and its complete imported chain remain unchanged.

## Full telescope and mathematical meaning

There are no external term or instance parameters. The entire body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔
    ∃ z : Lˣ, x = y * normUnits K L z
```

All seven universal binders are internal and retain the source order:

| Position | Binder | Kind and role |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure on `K` |
| 4 | `[Field L]` | Instance-implicit field structure on `L` |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `(x : Kˣ)` | Explicit first base-field representative |
| 7 | `(y : Kˣ)` | Explicit second base-field representative |

The sole universe parameter `u` is arbitrary and shared by `K` and `L`.
The representatives `x` and `y` are universally quantified units of `K`.
The left side equates their images under the canonical norm-quotient
projection. The right side quantifies an existential witness `z : Lˣ`,
a unit of the extension field, and requires an equality in `Kˣ`.
In that equality, `x` is alone on the left; the right side is the product
whose left factor is `y` and whose right factor is the actual unit norm
`normUnits K L z`. Both implications are asserted, including the
existence of such a witness from equality of classes. Given a proof `H`
of this closed proposition, `H K L x y` would supply the equivalence.

There is no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise. The inherited constructions
in `Langlands.NYLL.LocalFieldTheory` have the following concrete meanings:

| Declaration | Meaning and public module |
| --- | --- |
| `normUnits K L` | `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, from `LocalField.NormUnits.U002.Definitions` |
| `localNormSubgroup K L` | The actual image `(normUnits K L).range`, from `NormQuotient.U001.Definitions` |
| `NormQuotient K L` | `Kˣ ⧸ localNormSubgroup K L`, from `NormQuotient.U002.Definitions` |
| `normClass K L` | The canonical homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`, from `NormQuotient.U005.Definitions` |

In this table `LocalField` abbreviates the module prefix
`Langlands.NYLL.ValuedFieldTheory.LocalField`, and `NormQuotient`
abbreviates its `NonarchimedeanLocalField.NormQuotient` branch.
The quotient commutative group structure is inherited from U003.Definitions.
The existential therefore uses the actual algebra unit norm and its
image; these definitions and the projection are reused unchanged.
The host `Langlands.LocalClassField.NormQuotient` has a separate
finite-dimensionality parameter and is not used by this assertion.

## Source pin, declaration map and related assertions

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:350–362`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L350-L362).
Lines 350–351 contain the retained docstring, 352 introduces
`normClass_eq_iff_exists_norm_mul_right` and `K L`, 353 supplies the
instances and explicit representatives, 354–355 state the equivalence,
and 356–362 give the original proof. The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

The original norm subgroup, quotient, group structure and projection
are at 26–54 of that file. The actual unit norm is at 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file
SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1237 read the passage, the related source assertions and both
retained originals' headers and recomputed both whole-file hashes on
6 November 2026 UTC.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_iff_exists_norm_mul_right` | Closed `NormClassEqIffExistsNormMulRightStatement.{u}` in this module |
| Proof `normClass_eq_iff_exists_norm_mul_right` | Deferred exact proof with the adapted source name |
| `normClass_eq_iff_exists_norm_mul_left` | Public theorem of `NormClassEqIffExistsNormMulLeftStatement.{u}` in U038.Proofs |
| `normClass_mul_normUnits` | Public theorem of `NormClassMulNormUnitsStatement.{u}` in U033.Proofs |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with the same meanings |

The adaptation adds the namespace prefix, names the assertion
`NormClassEqIffExistsNormMulRightStatement`, and moves the full telescope
into a closed Prop-valued definition. Shared `u`, all binder kinds and
order, explicit `x y`, the extension-unit witness and the witness
equation's orientation are preserved. The sole U038.Proofs import
replaces the source import list. The unused universe `v`, noncomputable
section, truth proof and unrelated declarations are omitted. No instance
or simp registration is added. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places M093.039 after M093.038.END. No patch10 edit applies to M093.

The already public U038 left-multiplication existential
`NormClassEqIffExistsNormMulLeftStatement.{u}` (source lines 335–340)
has the same seven universal binders and the same class-equality left
side. Its right side is `∃ z : Lˣ, x = normUnits K L z * y`, with the
unit norm as the left factor; the present assertion places it as the
right factor. The public U033 class identity
`NormClassMulNormUnitsStatement.{u}` (source lines 295–298) instead has
explicit `(x : Kˣ) (z : Lˣ)` after the same five type and instance
binders and states
`normClass K L (x * normUnits K L z) = normClass K L x`, i.e. right
multiplication by a unit norm preserves the class. Both public statements
and their proofs are available through the unchanged linear chain to
U038.Proofs.

The original M093.039 proof uses the U038 left-multiplication
equivalence to obtain a witness `z` with `x = normUnits K L z * y` in
the forward direction, then reorders the product by `simpa [mul_comm]`;
`Kˣ` is commutative and environment Mathlib
`Mathlib/Algebra/Group/Semigroup.lean:228` states
`mul_comm : ∀ a b : G, a * b = b * a`. Its backward direction rewrites
`x` by the witness equation and applies the U033 identity to `y` and
`z`. This describes the source provenance and relation between
assertions. This pair contains no truth proof of the new proposition;
the exact proof of `normClass_eq_iff_exists_norm_mul_right` follows
independent statement publication.

The retained source belongs to registration
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths under `notes/errata/` were checked in the
workspace, project and supplied Library on 6 November 2026 UTC; all
six paths were absent.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 1237's dated modification
record. Worker 1237 authored this extraction and companion directly
from the pinned original, following the structure of the public U038
statement pair. No unpublished project draft or patch10 edit was reused,
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
inspection provide development evidence. Acceptance and publication
under `lean.statement@1` require independent semantic review and integration.

Only the statement phase of M093.039 is covered. Its truth proof,
M093.040 onward and host adapters remain separate work. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the one named Artin
family, actual norm image and exact norm kernel, host quotient evaluation
and bijectivity, actual quotient topology, finite discrete Galois topology
and both continuity directions for every prime and arbitrary supplied
`TF` and `TE`. Type 0 is an intermediate host stage. Normalization,
inertia, universe transport, cohomological comparison and reciprocity
results still require separate work. Existing cohomological definitions
and frozen proof targets retain their meanings.
