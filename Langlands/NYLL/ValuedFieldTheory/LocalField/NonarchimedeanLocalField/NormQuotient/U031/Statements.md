# Equal norm classes and unit-norm ratios

This module defines the single closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqIffExistsNormDivStatement.{u} : Prop`.
It records the asserted type of M093.031 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U030.Proofs`.
That module and its entire published dependency chain remain unchanged.

## Complete closed telescope

The definition has no external term or instance parameters and retains
exactly one arbitrary universe `u`. Its entire body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔
    ∃ z : Lˣ, x / y = normUnits K L z
```

All seven binders are internal to the proposition, in this order:

| Binder | Kind and meaning |
| --- | --- |
| `K : Type u` | Explicit base field type |
| `L : Type u` | Explicit extension field type in the same universe |
| `[Field K]` | Instance-implicit field structure on `K` |
| `[Field L]` | Instance-implicit field structure on `L` |
| `[Algebra K L]` | Instance-implicit algebra structure |
| `(x : Kˣ)` | Explicit first unit of the base field |
| `(y : Kˣ)` | Explicit second unit of the base field |

Every binder is quantified inside the proposition; none is an assumed
parameter of the definition. There is no finite-dimensionality,
finite-module, valuation, topology, local-field, separability or Galois
premise. The module's local-field location does not restrict this
generic algebraic assertion.

## The existential ratio criterion

The left side of the equivalence is equality of the two norm classes in
`NormQuotient K L`. The right side asserts that some unit `z : Lˣ` of
the extension field exists with `x / y = normUnits K L z`. The ratio
`x / y` is division in the group `Kˣ` of base-field units, given by
Mathlib's `Units` division, so `x / y = x * y⁻¹`. It is formed in `Kˣ`,
not in `K`. The witness `z` is a unit of `L`, not an arbitrary element
of `L`. The witness equation has the source orientation: the ratio is on
the left and the unit norm of `z` is on the right. Both directions of the
equivalence are asserted.

The order of the two units matters for the displayed equation but not
for its truth: if `x / y = normUnits K L z`, then
`y / x = normUnits K L z⁻¹`, because `normUnits K L` is a group
homomorphism. The statement uses only the displayed order.

## Actual norm image and quotient projection

The public `Langlands.NYLL.LocalFieldTheory.normUnits`, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`,
is `Units.map (Algebra.norm K) : Lˣ →* Kˣ`, so the coercion of
`normUnits K L z` to `K` is `Algebra.norm K (z : L)`. Its field universes
are independent, and it has no finiteness premise. Here it is specialized
to the shared universe `u`. When `L` has no `K`-basis indexed by a finite
set, Mathlib's `Algebra.norm` is identically `1`
(`Algebra.norm_eq_one_of_not_exists_basis` in
`Mathlib/RingTheory/Norm/Defs.lean`). Then the only unit norm is `1`, and
the right side says `x = y`. The assertion therefore remains meaningful
without a finiteness premise.

The public `localNormSubgroup`, in `NormQuotient.U001.Definitions`, is
exactly `(normUnits K L).range`, the actual image of the unit norm. The
public `NormQuotient`, in U002.Definitions, is
`Kˣ ⧸ localNormSubgroup K L`, with its existing U003 commutative-group
structure `normQuotientCommGroup`. The public `normClass`, in
U005.Definitions, is the canonical homomorphism
`QuotientGroup.mk' (localNormSubgroup K L) : Kˣ →* NormQuotient K L`.
The equality on the left is equality in this actual quotient. Thus the
assertion says that two base-field units have the same class modulo the
image of the unit norm exactly when their ratio is the unit norm of an
extension-field unit. These constructions are reused unchanged.

The host `Langlands.LocalClassField.NormQuotient` has a
finite-dimensionality parameter and does not replace this general
support interface.

## Relation to the public membership criterion

The already public `normClass_eq_iff_div_mem` in
`NormQuotient.U019.Proofs` proves `NormClassEqIffDivMemStatement.{u}`,
whose body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔ x / y ∈ localNormSubgroup K L
```

It is inherited through the unchanged U030 chain. Mathlib's
`MonoidHom.mem_range` turns membership `x / y ∈ (normUnits K L).range`
into `∃ z, normUnits K L z = x / y`. That equation has the reverse
orientation of this statement. M093.031 states the same criterion with
an explicit `Lˣ` witness and the source orientation `x / y = normUnits K L z`.

## Assertion and deferred truth proof

This file defines the proposition and contains no proof of its truth.
The later exact proof is reserved as
`Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_exists_norm_div`, with
type `NormClassEqIffExistsNormDivStatement.{u}`. No instance or simp
registration is installed here.

The source proof of M093.031 rewrites with `normClass_eq_iff_div_mem`,
changes the membership to membership in `(normUnits K L).range`,
rewrites with `MonoidHom.mem_range`, and proves both implications by
reversing the witness equation. This records the source proof route and
the available public dependency; the separate truth proof remains
deferred.

## Pinned original and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:274–286`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L274-L286):
docstring at 274, theorem name with `K L` at 275, the three structures
and the units `x y` at 276, the norm-class equality at 277, the
existential ratio condition at 278, and the omitted proof at 279–286.
Its asserted type is

```lean
theorem normClass_eq_iff_exists_norm_div (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x / y = normUnits K L z
```

The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The norm subgroup, quotient, group structure and canonical projection
are at 26–54, and the reused `normClass_eq_iff_div_mem` is at 183–190.
The support norm originates in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`. That complete
original file was also read; its SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Telescope and asserted conclusion of `normClass_eq_iff_exists_norm_div` | Closed `NormClassEqIffExistsNormDivStatement.{u}`, defined here |
| `normUnits` and `localNormSubgroup` | Existing public norm-image constructions, unchanged |
| `NormQuotient` and `normQuotientCommGroup` | Existing public quotient and group structure, unchanged |
| `normClass` | Existing public canonical projection, unchanged |
| `normClass_eq_iff_div_mem` | Existing public U019.Proofs theorem, unchanged |
| Truth proof of `normClass_eq_iff_exists_norm_div` | Deferred exact theorem with the adapted source name |

Worker 248 extracted the asserted type directly from the pinned
original on 2 November 2026 and wrote this companion. The namespace
gains the `Langlands.NYLL` prefix and all seven original binders move
inside a closed Prop-valued definition, preserving their order and
binder kinds. The original docstring is retained on the definition.
The sole U030.Proofs import preserves the published chain. The truth
proof, original noncomputable section, unused universe `v` and
unrelated declarations are omitted. A proposition definition needs no
noncomputable section. M093 has no patch10 change. No shared
adaptation draft or another worker's unpublished work was reused.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The errata paths `notes/errata/<source id>.md` for both source IDs were
checked in the workspace, project and supplied Library; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and remaining obligations

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, with an explicit dated modification record. There are no other
project coauthors or reused-draft contributors; dependency authors and
notices remain unchanged. The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`;
they match the originals, including inherited dependency notices.

The exact truth proof requires a separate proof phase after this
statement is independently accepted and published. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains one named
`abelianLocalArtinMap` family for every prime and arbitrary supplied
`TF`/`TE`, with the actual unit-norm image, exact norm kernel, quotient
topology, finite discrete Galois topology, host quotient construction,
evaluation, bijectivity and both continuity directions. Type 0 is the
initial host stage and does not discharge arbitrary-universe transport.
This generic support statement supplies no normalization, inertia,
universe transport, cohomological comparison or reciprocity theorem.
Existing cohomological definitions and frozen targets retain their
meaning. M093.032 and later units and host adapters remain separate work.
Compilation alone establishes neither independent semantic acceptance
nor publication.
