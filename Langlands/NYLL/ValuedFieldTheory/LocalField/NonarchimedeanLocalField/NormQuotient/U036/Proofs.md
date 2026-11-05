# Equal norm classes from left multiplication by a unit norm

This module proves the independently published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOfEqNormUnitsMulStatement.{u}`
by the theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_of_eq_normUnits_mul`.
The theorem's unapplied type is exactly that proposition, with no external
term or instance parameters. The shared universe `u` is arbitrary.

Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U036.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged. The proof uses only their existing constructions and theorems.

## Target and mathematical meaning

Unfolding the published assertion gives

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] {x y : Kˣ} (z : Lˣ)
  (h : x = normUnits K L z * y), normClass K L x = normClass K L y
```

The nine internal binders keep their source order: explicit `K`, explicit `L`,
the instance arguments `[Field K]`, `[Field L]`, `[Algebra K L]`, implicit
representatives `{x : Kˣ}`, `{y : Kˣ}`, explicit `(z : Lˣ)`, and the named
hypothesis `(h : x = normUnits K L z * y)`. The product in `h` has the unit
norm as its left factor and `y` as its right factor. Both sides of the
conclusion are canonical quotient projections of base-field units.

The inherited `normUnits K L` is the actual algebra norm on units,
`Units.map (Algebra.norm K)`. The subgroup `localNormSubgroup K L` is its
range, `NormQuotient K L` is `Kˣ ⧸ localNormSubgroup K L`, and
`normClass K L` is `QuotientGroup.mk' (localNormSubgroup K L)`.
Their existing definitions and the inherited quotient commutative group
structure are reused unchanged. A factor in the image of the unit norm
has identity quotient class. Thus multiplying `y` by the norm of `z`
yields a representative of the same quotient class; the equality `h`
identifies that representative with `x`.

There are no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premises. In particular the support
construction retains its general field-algebra signature. The separate
finite-dimensional host norm quotient is not substituted for it.

## Implemented proof

The complete proof body is

```lean
  intro K L _ _ _ x y z h
  rw [h, normClass_normUnits_mul]
```

The introductions expose all nine binders of the closed assertion in their
original order, including its three typeclass structures. First rewriting
with `h` changes the left side of the goal to
`normClass K L (normUnits K L z * y)`. The inherited public theorem
`Langlands.NYLL.LocalFieldTheory.normClass_normUnits_mul` from U032.Proofs,
available through the unchanged U036 statement import, rewrites that
expression to `normClass K L y`. Reflexivity closes the resulting equality.
This is the original proof route, preceded by introductions needed for the
published closed proposition. No additional hypothesis, instance, simp
registration or auxiliary declaration is introduced.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact source passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:318–325`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L318-L325).
Line 318 opens the section, 320 is the retained docstring, 321 introduces
the theorem name and `K L`, 322 supplies the three instances, implicit
representatives and explicit unit, 323 is the named hypothesis `h`,
324 is the conclusion, and 325 is `rw [h, normClass_normUnits_mul]`.
The whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The inherited left-multiplication theorem is at lines 288–293; the subgroup,
quotient, group structure and projection are at lines 26–54.

The actual unit norm is defined at lines 32–34 of
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, whose whole-file SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
Worker 1560 read both complete retained original files and recomputed their
hashes on 5 November 2026 UTC.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_of_eq_normUnits_mul` | Published closed `NormClassEqOfEqNormUnitsMulStatement.{u}` in U036.Statements |
| Proof `normClass_eq_of_eq_normUnits_mul` | This exact theorem of the same adapted name in U036.Proofs |
| `normClass_normUnits_mul` | Existing public U032.Proofs theorem, reused through the unchanged import chain |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normClass` | Existing public constructions with their original meanings |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published U036.Statements import, and proves
its closed proposition rather than restating the telescope as external
parameters. The nine introductions recover the source context and retain
the original two rewrites. The unused universe `v`, noncomputable section
and unrelated declarations are omitted. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places this proof at M093.036 after M093.035.END. No patch10 edit applies
to M093.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths under `notes/errata/` were checked in the
workspace, project and supplied Library on 5 November 2026 UTC; all six
paths were absent.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 1560's dated modification
record. Worker 1560 authored this proof extraction and companion directly
from the pinned original and the published statement and inherited proof.
No unpublished project draft or patch10 edit was reused. There are no
project coauthors for this pair.

The unchanged inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE), including applicable
dependency attribution, are retained in `repository_paths`. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Development compilation is
separate from acceptance. Publication under `lean.proof@1` requires the
Lake/kernel/exact-target and unchanged-statement/frozen-dependency checks,
independent semantic review, and Integrator publication.

This proof covers only the generic algebraic support identity M093.036.
M093.037 onward and host adapters are separate work. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the named Artin family,
exact norm kernel, surjectivity, host quotient evaluation and bijectivity,
actual quotient topology, finite discrete Galois topology and both
continuity directions for every prime and arbitrary supplied `TF` and `TE`.
Type 0 is an intermediate host stage. Normalization, inertia, universe
transport and comparison with the cohomological route remain separate
obligations. Existing cohomological definitions and frozen targets retain
their meanings.
