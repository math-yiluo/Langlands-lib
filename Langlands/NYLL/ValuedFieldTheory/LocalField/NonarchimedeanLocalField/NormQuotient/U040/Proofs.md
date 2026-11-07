# Equal norm classes under a surjective unit norm

The theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_all_of_normUnits_surjective`
proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqAllOfNormUnitsSurjectiveStatement.{u}`.
Its entire unapplied type is that proposition; it has no external term
or instance parameters. This is the proof of M093.040 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U040.Statements`.
That published Lean/Markdown pair and its complete imported chain are
unchanged.

## Target and mathematical meaning

Unfolding the published proposition gives

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
  (h : Function.Surjective (normUnits K L)) (x y : Kˣ),
  normClass K L x = normClass K L y
```

All eight universal binders are internal and retain the source order
and kinds:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | explicit base-field type |
| 2 | `L : Type u` | explicit extension-field type |
| 3 | `[Field K]` | instance-implicit |
| 4 | `[Field L]` | instance-implicit |
| 5 | `[Algebra K L]` | instance-implicit |
| 6 | `h : Function.Surjective (normUnits K L)` | explicit named surjectivity hypothesis |
| 7 | `x : Kˣ` | explicit first representative |
| 8 | `y : Kˣ` | explicit second representative |

The sole universe parameter `u` is arbitrary and shared by the fields.
The hypothesis `h` says that the actual homomorphism
`normUnits K L : Lˣ →* Kˣ`, coerced to a function, is surjective: every
base-field unit is the unit norm of some extension-field unit. The
representatives `x` and `y` are arbitrary base-field units quantified
after `h`. The conclusion equates their canonical projections in
`NormQuotient K L`. Thus, when every unit is a norm, the norm quotient
has a single class. Applying
`normClass_eq_all_of_normUnits_surjective K L h x y` supplies this
equality.

The unchanged inherited constructions have the concrete meanings

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L = QuotientGroup.mk' (localNormSubgroup K L)
```

The final identity uses the named quotient type. These constructions
come respectively from NormUnits.U002.Definitions and
NormQuotient.U001.Definitions, U002.Definitions and U005.Definitions
under `Langlands.NYLL.ValuedFieldTheory.LocalField`, with NormQuotient
in its NonarchimedeanLocalField branch. U003.Definitions supplies the
quotient commutative group structure. Thus the hypothesis concerns the
actual norm of extension units, and the conclusion the canonical
quotient by its image.

There are no finite-dimensionality, finite-module, local-field,
separability, Galois, valuation or topology premises. The general
algebra norm convention is inherited without restriction. The separate
host norm quotient with a finite-dimensionality parameter is not used.

## Implemented proof

The complete proof body is

```lean
  intro K L _ _ _ h x y
  apply (normClass_eq_iff_div_mem K L x y).2
  exact MonoidHom.mem_range.mpr (h (x / y))
```

The introductions expose the eight internal binders, making the field
and algebra structures available as local instances and keeping the
source name `h` for the surjectivity hypothesis. The public U019
theorem `normClass_eq_iff_div_mem`, whose unapplied type is
`NormClassEqIffDivMemStatement.{u}`, states for `K L x y` that
`normClass K L x = normClass K L y ↔ x / y ∈ localNormSubgroup K L`.
Applying its reverse implication reduces the goal to the membership
`x / y ∈ localNormSubgroup K L`.

Surjectivity applied to the base-field unit `x / y` gives
`h (x / y) : ∃ a, normUnits K L a = x / y`. The Mathlib theorem
`MonoidHom.mem_range : y ∈ f.range ↔ ∃ x, f x = y` turns this witness,
through `.mpr`, into `x / y ∈ (normUnits K L).range`. Because
`localNormSubgroup K L` is defined as `(normUnits K L).range`, this term
closes the goal by definitional unfolding. The theorem
`normClass_eq_iff_div_mem` is inherited through the unchanged chain
U019.Proofs to U040.Statements.

After the introductions required by the closed proposition, this is
the original two-line proof. No helper declaration, added premise,
instance or simp registration is introduced. Development compilation
in the approved environment reported no errors or warnings, the single
universe parameter `u`, and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Pinned original and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:364–370`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L364-L370).
Line 364 contains the retained docstring, 365 introduces the theorem
and `K L`, 366 supplies the three instances, 367 gives the named
hypothesis `h` followed by explicit `x y`, 368 states the conclusion,
and 369–370 give the retained proof

```lean
  apply (normClass_eq_iff_div_mem K L x y).2
  exact MonoidHom.mem_range.mpr (h (x / y))
```

The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The source equality criterion `normClass_eq_iff_div_mem` begins at
line 184, and the subgroup, quotient, group structure and projection
occur at 26–54.

The actual unit norm is at 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file
SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 248 read the original header and these passages and recomputed
both whole-file hashes on 6 November 2026 UTC. The approved Mathlib
source `Mathlib/Algebra/Group/Subgroup/Ker.lean:77–79` states
`MonoidHom.mem_range {f : G →* N} {y : N} : y ∈ f.range ↔ ∃ x, f x = y`,
proved by `Iff.rfl`; it is reused through the inherited imports without
copying Mathlib source.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_all_of_normUnits_surjective` | Published closed `NormClassEqAllOfNormUnitsSurjectiveStatement.{u}` in U040.Statements |
| Proof `normClass_eq_all_of_normUnits_surjective` | This theorem of the same adapted name in U040.Proofs |
| `normClass_eq_iff_div_mem` | Published U019.Proofs theorem reused through the unchanged chain |
| `MonoidHom.mem_range` | The same Mathlib theorem in the approved environment |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with their original meanings |

The adaptation prefixes the namespace, replaces the source imports by
the sole U040.Statements import, and names the closed published
proposition as the theorem type. The eight introductions recover the
original context before its unchanged proof. The unused universe `v`,
noncomputable section and unrelated declarations are omitted.
The partition places M093.040 after M093.039.END. No patch10 edit applies
to M093. Worker 1736 authored the imported statement pair. Worker 248
adapted this proof directly from the pinned original and published
dependencies; no unpublished project draft is reused and there are no
project coauthors for this pair.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked under `notes/errata/` in
the workspace, project and supplied Library on 6 November 2026 UTC;
all six paths were absent.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 248's dated modification
record. The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
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

This proof covers the generic norm-quotient support identity M093.040.
M093.041 (`normClass_eq_of_localNormSubgroup_eq_top`) and host adapters
remain separate work. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the named Artin family,
exact norm kernel, surjectivity, host quotient evaluation and bijectivity,
actual quotient topology, finite discrete Galois topology and both
continuity directions for every prime and arbitrary supplied `TF` and `TE`.
Type 0 is an intermediate host stage. Normalization, inertia, universe
transport and cohomological comparison remain separate obligations.
Existing cohomological definitions and frozen targets keep their meanings.
