# Restricting valuation subrings to intermediate fields: statements

The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.Statements`
defines four closed propositions in the namespace
`Langlands.NYLL.RamificationTheory.ValuationSubring`. They state exactly the
theorems M233.005, M233.006, M233.007 and M233.010 of Naganori Yamaguchi's
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean).
The complete original file has SHA-256
`bc2b582cac15fc4a9c6dc94e9687368e2a1bf91ca9d4111d41a9458fe8e49889`.
I read the whole original file (344 lines). The parts used are:

- the ambient namespaces and universes (lines 53–64);
- section `RestrictIntermediateField` (from line 110) with its variables
  `{K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]` (line 112);
- the four theorems, at lines 120–124, 126–130, 132–148 and 170–190;
- `open scoped Pointwise` (line 150).

The module states these propositions without proving them. The proofs, under
the adapted source names and with the source's `@[simp]` attributes, are
separate proof units.

| Unit | Source theorem (lines) | Closed target | Universes | Form |
| --- | --- | --- | --- | --- |
| M233.005 | `restrictIntermediateField_eq_comap` (120–124, `@[simp]`) | `restrictIntermediateField_eq_comapStatement` | `u, v` | `abbrev` |
| M233.006 | `mem_restrictIntermediateField_iff` (126–130, `@[simp]`) | `mem_restrictIntermediateField_iffStatement` | `u, v` | `abbrev` |
| M233.007 | `restrictIntermediateField_hasExtension` (132–148) | `restrictIntermediateField_hasExtensionStatement` | `u, v, w` | `def` |
| M233.010 | `smul_hasExtension` (170–190) | `smul_hasExtensionStatement` | `u, v, w` | `def` |

Every target has type `Prop` and no parameters outside its body. The
universes are those of the source: `u` for the base field `K`, `v` for the
ambient field `Ω`, and `w` for the value group `Γ`. In every body:

- `K` and `Ω` are implicit;
- the field and algebra structures are instance binders;
- the remaining binders keep the source's binder kinds and order.

`restrictIntermediateField` is the published M233.004 definition in the same
namespace: the preimage of a valuation subring `A` of `Ω` under the inclusion
of an intermediate field `E` of `Ω / K`.

## M233.005: the restriction is a comap

```lean
∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  (A : _root_.ValuationSubring Ω) (E : IntermediateField K Ω),
  (restrictIntermediateField A E) = A.comap (algebraMap E Ω)
```

This is an equality of valuation subrings of `E`. The right side is Mathlib's
`ValuationSubring.comap` along the inclusion `algebraMap E Ω`. It records the
definition of M233.004 as a rewrite rule.

## M233.006: membership in the restriction

```lean
∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  (A : _root_.ValuationSubring Ω) (E : IntermediateField K Ω) (x : E),
  x ∈ (restrictIntermediateField A E) ↔ (x : Ω) ∈ A
```

An element `x` of `E` lies in the restriction exactly when its image `(x : Ω)`
in the ambient field lies in `A`.

## M233.007: restrictions of extensions are extensions

```lean
∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
  (v : _root_.Valuation K Γ) (A : _root_.ValuationSubring Ω)
  [_root_.Valuation.HasExtension v A.valuation]
  (E : IntermediateField K Ω),
  _root_.Valuation.HasExtension v ((restrictIntermediateField A E)).valuation
```

The source places `{Γ : Type w} [LinearOrderedCommGroupWithZero Γ]` after the
section variables, and the closed body does the same.

- `v` is an arbitrary Mathlib valuation on `K` with values in `Γ`.
- `A.valuation` is the canonical valuation of the valuation subring `A`.
- `Valuation.HasExtension v w` is Mathlib's predicate for valuations on `K`
  and on a `K`-algebra. It says that `w (algebraMap K _ a) ≤ w (algebraMap K _ b)`
  if and only if `v a ≤ v b`, for all `a, b : K`.

The statement says: if the valuation of `A` extends `v`, then for every
intermediate field `E`, the valuation of the restriction of `A` to `E` also
extends `v`. Here `E` is a `K`-algebra through Mathlib's `IntermediateField`
structure. The hypothesis is an instance binder, as in the source.

## M233.010: Galois translates of extensions are extensions

```lean
∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
  (v : _root_.Valuation K Γ) (A : _root_.ValuationSubring Ω)
  [_root_.Valuation.HasExtension v A.valuation]
  (σ : Ω ≃ₐ[K] Ω),
  _root_.Valuation.HasExtension v (σ • A).valuation
```

The target is written under `open scoped Pointwise`, as in the source.
`σ • A` is Mathlib's pointwise action of the `K`-algebra automorphism group of
`Ω` on its valuation subrings: the image of `A` under `σ`. The statement says
that if the valuation of `A` extends `v`, then so does the valuation of every
translate `σ • A`.

## Why two targets are `abbrev`

The source marks M233.005 and M233.006 `@[simp]`, and the task keeps that
attribute on their proofs. Each proof is a theorem whose type is the closed
target. `simp` builds its rewrite rules after unfolding the type only at
reducible transparency. With a plain `def` target, the attribute would
register a useless rule; a `lean_check` trial showed `simp` made no progress.
As an `abbrev`, the target unfolds to the source equality or equivalence, so
the attribute gives the source's rewrite rule. Trial proofs checked that
`simp`, `simp only [...]` and `rw [...]` all work with these `abbrev` targets.
The other two targets are ordinary `def`s; the source does not mark them
`@[simp]`.

## Source correspondence and modifications

- **Statements.** Each theorem's statement is kept, with the section
  variables and its own binders, as the body of a closed proposition named by
  the source theorem name with the suffix `Statement`. This is an
  organizational adaptation, not a new assertion. Its mathematical content is
  exactly the source statement.
- **Omitted for the proof units.** The proofs and the `@[simp]` attributes
  are left to the separate proof units, which use the adapted source names
  `Langlands.NYLL.RamificationTheory.ValuationSubring.<source name>`.
- **Names.** The namespace gains the prefix `Langlands.NYLL`. Mathlib's
  `ValuationSubring` and `Valuation` are written with `_root_`. In the source
  they resolve to the same Mathlib declarations, since NYLL declares no type
  with either name.
- **Imports.** The upstream imports are replaced by the published M233.004
  module `…FiniteLevelValuationRestriction.RestrictIntermediateField` and
  `Mathlib.RingTheory.Valuation.Extension`, which supplies
  `Valuation.HasExtension`. The pointwise action instance comes in through
  these imports.
- **Omitted source lines.** The source's `open ValuationTheory`, its
  Henselian `open` (55–56), and the `noncomputable section` are omitted. The
  statements do not use them.

The other commands of the source module are outside these targets:

- M233.001–.003;
- M233.008 `mem_inv_smul_iff_apply_mem`;
- M233.009 `mem_smul_valuationSubring_iff`;
- M233.011 `restrictIntermediateField_smul_hasExtension`;
- the separable-power lemmas.

Searches of Mathlib and the Library found no existing declaration for these
four statements.

## Attribution

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by the original path
above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
public port partition `notes/reuse/nyll-public-port/m217-m240.md` lists these
rows and records no patch10 change for the source module. The workspace
`notes/errata` directory has no entry for this source. The NYLL NOTICE does
not list this source file among its third-party paths.

Original copyright and authorship are kept: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by
OpenAI Codex). Apache-2.0 applies. The existing verbatim
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean header records the modifications, made by Worker 122 on
13 November 2026. The approved environment is Lean 4.34.0 with Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
