# First-isomorphism equivalence on norm classes

This module proves
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSurjective_normClass`.
Its complete unapplied type is the already published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfSurjectiveNormClassStatement.{u,v}`.
This is the proof phase of M093.015 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Closed target and representative equation

The target internally quantifies over precisely this telescope and equation:

```lean
∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
  [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
  (hker : f.ker = localNormSubgroup K L) (x : Kˣ),
  normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x
```

All eleven term binders are inside the closed proposition. The fields `K`
and `L` share arbitrary universe `u`; the target group `M` lies in independent
arbitrary universe `v`. The type parameters are implicit, the four structure
parameters are instance-implicit, and `f`, `hf`, `hker`, and `x` are explicit
in the displayed order. The theorem has no external term parameters and
introduces no additional mathematical premise.

The sole direct import is the published U015 Statements module. Through its
U014 Definitions dependency it retains `M093.014.END` and the unchanged
named constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
normQuotientEquivOfSurjective f hf hker : NormQuotient K L ≃* M
```

Thus the quotient uses the actual unit-norm image, and `normClass K L x`
is the canonical class of the same representative `x` occurring in `f x`.
The kernel premise keeps the orientation `f.ker = localNormSubgroup K L`.
Only `Group M` is required; commutativity of `Kˣ` supplies normality of the
norm subgroup. No finite-dimensionality, finite-module, separability, Galois,
local-field, valuation or topology assumption is added.

In particular, the unrestricted `Algebra.norm K` convention is preserved.
Mathlib's `Algebra.norm_eq_one_of_not_module_finite` makes this norm
constantly one when `L` is not a finite `K`-module. The actual norm image
is then trivial, and the supplied `hker` requires a trivial kernel.
The theorem still covers that case.

## Implemented proof and simp behavior

The proof introduces the target's eleven binders, then follows the original
proof at lines 153–158 without changing its mathematical steps.
The `change` exposes the actual quotient and the defining composition

```lean
(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
  (QuotientGroup.quotientKerEquivOfSurjective f hf)
```

evaluated at `QuotientGroup.mk x`. The first factor transports from the
quotient by the actual norm image to the quotient by `f.ker`.
Rewriting `MulEquiv.trans_apply` exposes the composition's evaluation.
Rewriting `QuotientGroup.quotientMulEquivOfEq_mk` preserves the representative
through that subgroup-equality transport. The remaining canonical
first-isomorphism evaluation is definitionally `f x`, so `rfl` closes it.
The inverse of the imported equivalence uses classical choice of preimages;
the proof introduces no new choice construction.

The closed theorem itself has no `simp` attribute. A development experiment
registered that closed theorem directly, but ordinary `simp` made no progress
on the explicit representative equation. The declaration
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSurjective_normClass_apply`
therefore carries `@[simp]`. It has exactly the original telescope and
equation displayed above, and its entire proof is

```lean
normQuotientEquivOfSurjective_normClass f hf hker x
```

This convenience wrapper adds no premise and does not replace the exact
closed theorem. A separate private example with the original telescope
checks that ordinary `by simp` proves the representative equation after
importing this module. The private example is not part of this contribution.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The precise passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 146–158](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L146-L158):
docstring at 146, `simp` attribute at 147, theorem telescope/equation at
148–152, and proof at 153–158. The preceding constructor is at 137–144.
The complete original file was read and its SHA-256 verified as
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfSurjective_normClass` | `normQuotientEquivOfSurjective_normClass`, proving the closed published target |
| Same original theorem's explicit telescope and simp attribute | `normQuotientEquivOfSurjective_normClass_apply`, derived from the exact theorem |
| `LocalFieldTheory.normQuotientEquivOfSurjective` | Existing `normQuotientEquivOfSurjective` |
| `LocalFieldTheory.normClass` | Existing `normClass` |
| `LocalFieldTheory.NormQuotient` | Existing `NormQuotient` |
| `LocalFieldTheory.localNormSubgroup` | Existing `localNormSubgroup` |
| `LocalFieldTheory.normUnits` | Existing `normUnits` |

Only the first two rows introduce declarations here. Modifications by
Worker 1153 on 31 October 2026 are: add the `Langlands.NYLL` namespace
prefix; replace the source imports with the sole U015 Statements import;
give the exact theorem the closed published proposition as its type and
introduce its internal binders; move representative simplification to the
derived explicit-telescope wrapper; omit the unnecessary noncomputable
section and all other source declarations. The original theorem docstring
and proof steps are retained. The partition records no patch10 change to
this original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Neither source-ID errata file exists in the workspace, project or fixed
Library at the time of this extraction. Exact-name searches in the workspace
and current Library found only the published statement pair before this
proof was written. No audit draft was reused.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The relevant quotient API is at the approved Mathlib
`Mathlib/GroupTheory/QuotientGroup/Basic.lean`, lines 134–173.
Development compilation and declaration inspection succeeded with independent
`u` and `v` and only `propext`, `Classical.choice` and `Quot.sound`.
The ordinary-simp example also compiled. These checks do not establish
independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”,
released under Apache-2.0. The Lean file carries the dated modification record.
Worker 1153 adapted this proof directly from the pinned original and wrote this
companion. No other project worker supplied code or a reused draft for this
proof. Worker 107's existing statement and constructor are imported unchanged;
all 21 imported Library modules and their paired Markdown remain frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained in
`repository_paths` and were verified byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The inherited NOTICE's ValuedFieldTheory included-source list has no
NormQuotient-specific third-party entry. All inherited dependency notices and
attribution remain intact. No Mathlib implementation is copied into this file.

This conditional algebraic equation supplies no Artin map, kernel or
surjectivity proof for such a map, host quotient/evaluation adapter, or
topology theorem. M093.016 and later source units remain separate, and parent
finite reciprocity task `1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
