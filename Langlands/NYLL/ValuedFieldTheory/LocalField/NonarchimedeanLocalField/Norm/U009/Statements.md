# Norms of valuation integers

`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.algebraNorm_mem_integers_of_mem_integersStatement.{u, v}`
is the following closed proposition:

```lean
∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L]
  [Langlands.NYLL.LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]),
  Algebra.norm K (x : L) ∈ 𝒪[K]
```

The declaration is an ordinary definition of type `Prop` with no term
parameters. Its universe parameters are `u` and `v`, in that order, and they
are independent. The two fields are implicit, the six structures are instance
binders, and the element `x` is explicit, in the order listed. This artifact
states the proposition only; it does not prove it.

## Meaning

Under `open scoped ValuativeRel`, the notation `𝒪[K]` is Mathlib's
`Valuation.integer (ValuativeRel.valuation K)`
(`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`, line 88). This is the
subring of `K` of elements of valuation at most one, for the canonical
valuation of the valuative relation on `K`. An element `x : 𝒪[L]` is an element
of that subring of `L`, and `(x : L)` is its underlying element of `L`. Thus
the hypothesis named `of_mem_integers` in the original name is carried by the
type of `x`.

`Langlands.NYLL.LocalFieldTheory.ValuativeExtension K L` is the published NYLL
class from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension.Definitions`.
Its single field `integer_isIntegral` states that every element of `𝒪[L]`,
viewed in `L`, is integral over `𝒪[K]`. It is distinct from Mathlib's root
class `ValuativeExtension`, which compares valuative relations along the
algebra map. In this statement the namespaced class is the only link between
the valuations of `K` and `L`. The original writes it as
`LocalFieldTheory.ValuativeExtension`; inside the prefixed namespace that name
resolves to the published class. A private check confirmed that the elaborated
statement mentions `Langlands.NYLL.LocalFieldTheory.ValuativeExtension` and no
root `ValuativeExtension`.

The conclusion uses Mathlib's unrestricted `Algebra.norm K : L →* K`, the
determinant of left multiplication (`Mathlib/RingTheory/Norm/Defs.lean`,
lines 59–64). By `Algebra.norm_eq_one_of_not_module_finite` (line 76 of the
same file), it is constantly `1` when `L` is not a finite `K`-module. The
statement therefore has the stated meaning without a finiteness premise, as in
the original.

There is no finite-dimensionality, separability, Galois, local-field,
completeness, topology or valuation-comparison premise. The enclosing namespace
`IsNonarchimedeanLocalField` is inherited from the source; the statement does
not assume that either field is a local field.

## Source and adaptation

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean`, whose
SHA-256 is
`0e9e3d68b6d964addae89ea2185146fdee7c6b60bf23cfff679a20f34e808eb6`.
It is retained in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Lines 1–130 were read. Lines 1–12 give the header and imports, lines 20–30 the
namespace, universes, scoped openings and the variables `{K : Type u}
{L : Type v}`, lines 63–65 the `UnitNorm` section variables
`[Field K] [Field L] [Algebra K L]`, and lines 101–107 the lemma.

| Unit | Original declaration | Adapted statement |
| --- | --- | --- |
| M129.009, lines 101–107 | `LocalFieldTheory.IsNonarchimedeanLocalField.algebraNorm_mem_integers_of_mem_integers` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.algebraNorm_mem_integers_of_mem_integersStatement` |

The unit is listed with phase `S→P` in the published partition
`notes/reuse/nyll-public-port/m121-m144.md` (section M129). This module is its
statement phase.

Worker 176 made the following changes on 12 November 2026:

- The namespace is prefixed with `Langlands.NYLL`.
- The lemma's full type, including the section variables it uses, becomes the
  body of a `def : Prop`. The binder kinds and their order are unchanged.
- The universes are written as explicit parameters `.{u, v}` of the definition,
  replacing the file-level `universe u v` command, in the same order.
- The proof is omitted. The original name
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.algebraNorm_mem_integers_of_mem_integers`
  is left for the separate exact proof.
- `noncomputable section` and the unused `BigOperators` opening are omitted.
  Only `open scoped ValuativeRel`, which supplies the notation, is kept.
- The other source declarations of the file are omitted.

The original imports are `Mathlib.LinearAlgebra.Determinant`,
`Mathlib.RingTheory.Norm.Transitivity`, `Mathlib.RingTheory.Valuation.Integral`
and the NYLL modules `NormUnits`, `NonarchimedeanLocalField.ValuativeExtension`
and `NonarchimedeanLocalField.Basic`. They are replaced by two imports:

- The published `ValuativeExtension.Definitions`, which ports the NYLL
  `ValuativeExtension` module's class and instance and supplies `𝒪[·]`.
- `Mathlib.RingTheory.Norm.Defs`, which defines `Algebra.norm`.

The statement uses nothing else. `Determinant`, `Transitivity` and
`Valuation.Integral` are needed only by the original proof, which uses
`Algebra.isIntegral_norm` and `Valuation.Integers.mem_of_integral`. Neither
`NormUnits` nor `Basic` declares an instance, class, notation, coercion or
attribute other than `@[simp]`, so they cannot affect how the statement
elaborates. The earlier source declarations of the file, including
`mapBaseUnitsToExtensionUnits` (M129.004), do not occur in the statement.

No instance or other declaration is introduced besides the proposition.

## Relation to existing declarations

The published data definition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue`
(module `NonarchimedeanLocalField.Norm.U019.Definitions`) inlines the original
proof term of M129.009 at its membership field. It declares no theorem of this
name, so it neither supplies nor conflicts with this target.
The host theorem `Langlands.LocalClassField.PrimeGradedNorm.norm_integral`
proves a similar membership only for finite extensions of `p`-adic field
structures, under the additional hypotheses of its section. It does not cover
arbitrary valued fields with the namespaced integrality class. Searches of the
current Library, the approved Mathlib and the task list found no other statement
of this proposition. No applicable NYLL erratum was found in the published
errata.

## Development checks

In environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), the module list ending in this
module compiled with no errors or warnings. Inspection of the declaration
reports an ordinary definition, level parameters `u` and `v`,
`statement_returns_prop: true`, and only the assumptions `propext`,
`Classical.choice` and `Quot.sound`.

A private probe imported this module and all Mathlib modules of the source
import closure: the three listed above and `Mathlib.NumberTheory.LocalField.Basic`,
imported by the source's `Basic`. It reconstructed the original lemma in its
original section context with its original proof. The probe found the
following:

- The proposition's value and the reconstructed lemma's type are
  alpha-equivalent. They have the same level parameters `[u, v]` and
  identical binder kinds in the same order. They differ only in the
  automatically generated names of the anonymous instance binders.
- The reconstructed lemma proves the proposition, using only the same three
  assumptions.

These are development checks. They do not establish independent semantic
acceptance or publish a proof. The probe is excluded from this candidate.

## Attribution

The original copyright and author header is retained verbatim, including
"Naganori Yamaguchi (assisted by OpenAI Codex)". The source is Apache-2.0. The
unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are already published.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
NOTICE has no entry specific to this module. Worker 176 performed this
adaptation; no other worker's draft was reused.
