# Equal norm classes when the local norm subgroup is top

The theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_of_localNormSubgroup_eq_top`
proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOfLocalNormSubgroupEqTopStatement.{u}`.
Its entire unapplied type is that proposition; there are no external term
or instance parameters. This is the proof of M093.041, the final unit of
M093 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U041.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and mathematical meaning

Unfolding the published proposition gives

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
| 3 | `[Field K]` | Instance-implicit field structure |
| 4 | `[Field L]` | Instance-implicit field structure |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `(h : localNormSubgroup K L = ⊤)` | Explicit named subgroup-equality hypothesis |
| 7 | `(x : Kˣ)` | Explicit first representative |
| 8 | `(y : Kˣ)` | Explicit second representative |

The sole universe parameter `u` is arbitrary and shared by the two
fields. The hypothesis `h` says that the actual norm image is the top
subgroup of `Kˣ`, so every base-field unit belongs to it. The
representatives `x` and `y` are arbitrary units of `K`, quantified after
`h`. Their canonical projections to `NormQuotient K L` coincide.
Thus the quotient by the norm image has only one class.

The unchanged inherited constructions have their concrete meanings:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L = QuotientGroup.mk' (localNormSubgroup K L)
```

The last expression has the named quotient as codomain. These
constructions come respectively from NormUnits.U002.Definitions and
NormQuotient.U001.Definitions, U002.Definitions and U005.Definitions
under `Langlands.NYLL.ValuedFieldTheory.LocalField`, with NormQuotient
in its NonarchimedeanLocalField branch. U003.Definitions supplies the
quotient commutative group structure.

There are no finite-dimensionality, finite-module, local-field,
separability, Galois, valuation or topology premises. The general
algebra norm convention is inherited without restriction. The host
norm quotient with a finite-dimensionality parameter remains a separate
interface.

## Implemented proof

The complete proof body is

```lean
  intro K L _ _ _ h x y
  exact (normClass_eq_iff_div_mem K L x y).2 (by
    rw [h]
    exact Subgroup.mem_top (x / y))
```

The introductions expose all eight binders, installing the field and
algebra structures as local instances and preserving the name `h`.
The public U019 theorem `normClass_eq_iff_div_mem` has the closed type
`NormClassEqIffDivMemStatement.{u}`. Applied to `K L x y`, it says

```lean
normClass K L x = normClass K L y ↔ x / y ∈ localNormSubgroup K L
```

Its reverse implication reduces the desired equality to membership of
`x / y` in the norm image. Rewriting by `h` changes that membership to
`x / y ∈ (⊤ : Subgroup Kˣ)`. Mathlib's `Subgroup.mem_top (x / y)`
proves it. The U019 theorem reaches this module through the unchanged
chain ending in U041.Statements. After the introductions required by
the closed target, this is the original term proof. No helper
declaration, premise, instance or simp registration is introduced.

## Pinned original and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:372–378`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L372-L378).
Line 372 is the retained docstring; 373 introduces the theorem and
`K L`; 374 supplies the three instances, named hypothesis `h` and
explicit representatives `x y`; 375 is the conclusion; and 376–378
are the retained term proof. The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

The subgroup, quotient, group structure and projection are at lines
26–54 of that file, and the equality criterion is at 183–190.
The actual unit norm is at 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file
SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1766 read the original header and these NormQuotient passages,
the complete NormUnits source and recomputed both hashes on
7 November 2026 UTC. In the approved Mathlib source,
`Mathlib/Algebra/Group/Subgroup/Lattice.lean:142–144` states
`Subgroup.mem_top (x : G) : x ∈ (⊤ : Subgroup G)`, proved by
`Set.mem_univ x`. It is reused through the inherited imports.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_of_localNormSubgroup_eq_top` | Published closed `NormClassEqOfLocalNormSubgroupEqTopStatement.{u}` in U041.Statements |
| Proof `normClass_eq_of_localNormSubgroup_eq_top` | This theorem with the adapted source name in U041.Proofs |
| `normClass_eq_iff_div_mem` | Existing public U019.Proofs theorem inherited through U041.Statements |
| `Subgroup.mem_top` | The same Mathlib theorem in the approved environment |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with their original meanings |

The adaptation prefixes the namespace, replaces the original imports
with the sole U041.Statements import and names the published closed
proposition as the entire theorem type. The eight introductions recover
the original context before its unchanged proof. The original
noncomputable section, unused universe `v` and unrelated declarations
are omitted. No patch10 edit applies to M093.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths under `notes/errata/` were checked in the
workspace, project and supplied Library on 7 November 2026 UTC;
all six paths were absent.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 1766's dated modification
record. Worker 1766 adapted this proof from the pinned original and
published dependencies. No unpublished project draft is reused, and
there are no project coauthors.

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
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires
Lake/kernel/exact-target, unchanged-statement and frozen-dependency
checks, independent semantic review and Integrator publication.

This proof covers the generic support identity M093.041, the final
unit of M093 after M093.040. Host adapters remain separate work.
Parent task `1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the named
Artin family, exact norm kernel, surjectivity, host quotient evaluation
and bijectivity, actual quotient topology, finite discrete Galois
topology and both continuity directions for every prime and arbitrary
supplied `TF` and `TE`. Type 0 is an intermediate host stage.
Normalization, inertia, universe transport and cohomological comparison
remain separate obligations. Existing cohomological definitions and
frozen targets retain their meanings.
