# Equal norm classes and left multiplication by a unit norm

The theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_exists_norm_mul_left`
proves the independently published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqIffExistsNormMulLeftStatement.{u}`.
Its entire unapplied type is that proposition, with no external term or
instance parameters. This is the proof of M093.038 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U038.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and mathematical meaning

Unfolding the published assertion gives

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔
    ∃ z : Lˣ, x = normUnits K L z * y
```

All seven universal binders are internal and retain the original order
and kinds:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | explicit base-field type |
| 2 | `L : Type u` | explicit extension-field type |
| 3 | `[Field K]` | instance-implicit |
| 4 | `[Field L]` | instance-implicit |
| 5 | `[Algebra K L]` | instance-implicit |
| 6 | `x : Kˣ` | explicit first representative |
| 7 | `y : Kˣ` | explicit second representative |

The sole universe parameter `u` is arbitrary and shared by the fields.
The left side equates their canonical quotient projections. The right
side asks for an extension-field unit `z : Lˣ`; the equation is in `Kˣ`,
with `x` alone on the left and the actual unit norm of `z` as the left
factor multiplying `y` on the right. Both implications are proved.
Applying `normClass_eq_iff_exists_norm_mul_left K L x y` supplies the
equivalence, with `.1` giving a witness from equal classes and `.2`
giving class equality from a witness and its equation.

The unchanged inherited constructions have the concrete meanings

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L = QuotientGroup.mk' (localNormSubgroup K L)
```

The last identity uses the named quotient type. These constructions come
respectively from NormUnits.U002.Definitions and
NormQuotient.U001.Definitions, U002.Definitions and U005.Definitions under
the imported support prefix. U003.Definitions supplies the quotient
commutative group structure. Thus equality of quotient classes says
exactly that a norm in the actual image of `Lˣ` converts one
representative to the other in the prescribed order.

There are no finite-dimensionality, finite-module, local-field,
separability, Galois, valuation or topology premises. The general algebra
norm convention is inherited without restriction. The separate host norm
quotient with a finite-dimensionality parameter is not used.

## Implemented proof

The complete proof body is

```lean
  intro K L _ _ _ x y
  constructor
  · intro hxy
    rcases (normClass_eq_iff_exists_norm_div K L x y).1 hxy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← hz]
    exact (div_mul_cancel x y).symm
  · rintro ⟨z, hz⟩
    exact normClass_eq_of_eq_normUnits_mul K L z hz
```

The introductions expose all seven internal binders and make the three
structures available as local instances. The inherited public U031
theorem `normClass_eq_iff_exists_norm_div` has unapplied type
`NormClassEqIffExistsNormDivStatement.{u}`. Its forward implication
produces an extension unit `z` with `hz : x / y = normUnits K L z`.
Reuse this same witness. Rewriting the required equation by `← hz`
reduces it to `x = x / y * y`, which is the symmetry of the group
identity `div_mul_cancel x y`. This preserves the required factor order.

For the reverse direction, eliminate the existential to obtain `z` and
`hz : x = normUnits K L z * y`. The inherited public U036 theorem
`normClass_eq_of_eq_normUnits_mul`, whose unapplied type is
`NormClassEqOfEqNormUnitsMulStatement.{u}`, gives precisely the required
equality of norm classes. Its representatives are implicit; they are
inferred from `hz` and the goal. Both supporting theorems arrive through
the unchanged chain to U038.Statements.

This retains the original two-direction proof after the introductions
required by the closed proposition. No helper declaration, additional
premise, instance or simp registration is added.

## Pinned original and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:335–348`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L335-L348).
Lines 335–336 contain the retained docstring, 337 introduces the theorem
and `K L`, 338 gives the three instances and explicit representatives,
339–340 give the equivalence, and 341–348 give the retained proof.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The source division-form existential and proof are at 275–286, the
one-direction implication and proof at 320–325, and the subgroup,
quotient, group structure and projection at 26–54.

The actual unit norm is at 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file
SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1153 read both complete retained originals and recomputed their
hashes on 6 November 2026 UTC. The approved Mathlib source
`Mathlib/Algebra/Group/Defs.lean:89` states
`div_mul_cancel (a b : G) : a / b * b = a`; this group identity is reused
through the inherited imports, without copying Mathlib source.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_iff_exists_norm_mul_left` | Published closed `NormClassEqIffExistsNormMulLeftStatement.{u}` in U038.Statements |
| Proof `normClass_eq_iff_exists_norm_mul_left` | This theorem of the same adapted name in U038.Proofs |
| `normClass_eq_iff_exists_norm_div` | Published U031.Proofs theorem reused through the unchanged chain |
| `normClass_eq_of_eq_normUnits_mul` | Published U036.Proofs theorem reused through the unchanged chain |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with their original meanings |

The adaptation prefixes the namespace, replaces the source imports by
the sole U038.Statements import, and names the closed published
proposition as the theorem type. The seven introductions recover the
original context before its unchanged proof. The unused universe `v`,
noncomputable section and other source declarations are omitted.
The partition places M093.038 after M093.037.END. No patch10 edit applies
to M093, and no unpublished project draft is reused. Worker 1560 authored
the imported statement pair; Worker 1153 authored this proof pair
directly from the pinned original and published dependencies. There are
no project coauthors for this pair.

The retained original is in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked under `notes/errata/` in the
workspace, project and supplied Library on 6 November 2026 UTC; all six
paths were absent.

## Attribution, environment and scope

The Lean file preserves the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 1153's dated modification
record. The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, remain unchanged in `repository_paths`.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires the
Lake/kernel/exact-target, unchanged-statement and frozen-dependency checks,
independent semantic review and Integrator publication.

This proof covers the generic norm-quotient support identity M093.038.
M093.039 onward and host adapters remain separate work. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the named Artin family,
exact norm kernel, surjectivity, host quotient evaluation and bijectivity,
actual quotient topology, finite discrete Galois topology and both
continuity directions for every prime and arbitrary supplied `TF` and `TE`.
Type 0 is an intermediate host stage. Normalization, inertia, universe
transport and comparison with the cohomological route remain separate
obligations. Existing cohomological definitions and frozen targets keep
their meanings.
