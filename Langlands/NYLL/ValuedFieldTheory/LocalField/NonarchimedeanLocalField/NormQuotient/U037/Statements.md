# Equality of norm classes and multiplication by an inverse

The sole new declaration is the closed proposition definition
`Langlands.NYLL.LocalFieldTheory.NormClassEqIffMulInvMemStatement.{u} : Prop`.
It states that two base-field units have equal canonical norm classes exactly
when the first representative times the inverse of the second belongs to the
actual unit-norm image subgroup. This module defines the assertion; its truth
proof is deferred.

Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U036.Proofs`.
That published pair and its entire imported chain remain unchanged.

## Full telescope and mathematical meaning

The declaration has no external term or instance parameters. Its body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔ x * y⁻¹ ∈ localNormSubgroup K L
```

All seven binders are internal and retain their original order and kinds:

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
Both representatives are universally quantified units of `K`. The left side
is equality of their images under the canonical quotient homomorphism.
On the right side, the inverse `y⁻¹` is taken in `Kˣ`, and multiplication in
that group forms `x * y⁻¹` with `x` as the left factor and `y⁻¹` as the right
factor. Membership is tested before projection. Both directions are included:
equal norm classes imply this membership, and this membership implies equal
norm classes. Given a proof `H` of the closed proposition, `H K L x y`
would supply that equivalence.

There is no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise. The inherited constructions in
`Langlands.NYLL.LocalFieldTheory` retain their concrete meanings:

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
Thus membership of `x * y⁻¹` means that some extension unit `z : Lˣ`
satisfies `normUnits K L z = x * y⁻¹`. These public definitions are reused
unchanged. The host `Langlands.LocalClassField.NormQuotient` has a separate
finite-dimensionality parameter and is not used here.

## Source pin, declaration map and division form

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:327–333`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L327-L333).
Lines 327–328 contain the retained docstring, 329 introduces
`normClass_eq_iff_mul_inv_mem` and `K L`, 330 supplies the three instances
and explicit representatives, 331–332 give the equivalence, and 333 is
the original proof. The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

The original norm subgroup, quotient, group structure and projection are at
26–54 of that file. The actual unit norm is at 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1560 read both complete retained originals and recomputed their hashes
on 5 November 2026 UTC.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_iff_mul_inv_mem` | Closed `NormClassEqIffMulInvMemStatement.{u}` in this module |
| Proof `normClass_eq_iff_mul_inv_mem` | Deferred exact proof with the adapted source name |
| `normClass_eq_iff_div_mem` | Already public theorem of `NormClassEqIffDivMemStatement.{u}` in U019.Proofs |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with the same meanings |

The adaptation adds the namespace prefix, capitalizes the assertion's name
and appends `Statement`, and moves the full original telescope into the body
of a closed Prop-valued definition. It preserves shared `u`, all binder
kinds and order, explicit `x y`, and the product with the inverse in its
original orientation. The sole U036.Proofs import replaces the original
import list. The unused universe `v`, noncomputable section, truth proof
and unrelated declarations are omitted. No instance or simp registration
is added. The [public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places M093.037 after M093.036.END. No patch10 edit applies to M093.

The already public U019 division-form proposition has the same seven binders
and left side, and uses `x / y ∈ localNormSubgroup K L` on the right.
Its proof `normClass_eq_iff_div_mem` is inherited through the unchanged
linear chain to U036.Proofs. The original M093.037 proof rewrites division
as multiplication by an inverse using `div_eq_mul_inv` and that division-form
theorem. This explains the relation between the two assertions and records
the source route for a later proof task. This pair supplies no proof of the
new proposition; the exact proof follows independent statement publication.

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
from the pinned original. No unpublished project draft or patch10 edit was
reused, and there are no project coauthors for this pair.

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

Only the statement phase of M093.037 is covered. Its truth proof, M093.038
onward and host adapters remain separate work. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the one named Artin family,
actual norm image and exact norm kernel, host quotient evaluation and
bijectivity, actual quotient topology, finite discrete Galois topology
and both continuity directions for every prime and arbitrary supplied
`TF` and `TE`. Type 0 is an intermediate host stage. Normalization, inertia,
universe transport, cohomological comparison and reciprocity results still
require separate work. Existing cohomological definitions and frozen proof
targets retain their meanings.
