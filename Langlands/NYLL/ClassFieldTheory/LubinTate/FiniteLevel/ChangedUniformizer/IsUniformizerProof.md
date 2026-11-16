# Changed-uniformizer preservation proof: M391.003

This module proves the existing Library proposition
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer_isUniformizerStatement`
under the theorem name
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer_isUniformizer`.
The theorem's type is exactly that closed target, with independent universe
parameters `u v`. Its sole import is the actual target module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.Statements`.

The target quantifies over a field `K : Type u`, its field instance, the
published package `F : LocalField.{u, v} K`, an element
`π : F.valuationSubring`, a proof `hπ` that its image in `K` is a uniformizer
for `F.toCompleteDVF.valuation`, and a unit of the same valuation ring.
It asserts that the changed parameter, the unit times `π`, is a uniformizer
for that same chosen valuation. The original telescope, binder explicitness,
coercions and hypotheses are inherited from the unchanged target.

## Implemented proof

The proof introduces the six target binders, locally naming the unit `a`.
Mathlib's `associated_unit_mul_right π (a : F.valuationSubring) a.isUnit`
proves that `π` is associated to `(a : F.valuationSubring) * π` in the
valuation ring. Mathlib's `Valuation.IsUniformizer.of_associated`, applied
to `hπ`, then gives the uniformizer property of that product.

The published `standardLubinTateChangedUniformizer` is definitionally this
product, so Lean identifies the result with the target conclusion directly.
Source M391.002's defining equality is therefore unnecessary as a separate
lemma. The existing local-field package supplies the discrete valuation
instances required by `of_associated`; there are no new assumptions,
instances, constructions or helper declarations.

## Original source and correspondence

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`,
lines 69–76](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean#L69-L76),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Its complete source file has SHA-256
`684df6d32cebe6a70087c9d6e4c9d70ae6913407f3c6d1ee2d70a6c975b912f7`.
The readable pinned snapshot is registered under
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`. The source file was read
directly, and the project errata lookup contained no matching entry.

| Source unit | Original theorem | Adapted theorem |
| --- | --- | --- |
| M391.003, lines 69–76 | `LubinTate.standardLubinTateChangedUniformizer_isUniformizer` | `Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer_isUniformizer` |

The implemented mathematical proof is the original two-lemma proof at
lines 75–76. Its only proof adaptation is to introduce the universally
quantified binders of the published closed proposition and locally rename
the unit from `u` to `a`. It retains the actual published LocalField
structure and changed-parameter definition without editing either.

## Adaptations, attribution and verification

Worker 231 extracted this one proof on 16 November 2026, qualified its
namespace, replaced the twelve upstream imports with the exact statement
import above, replaced the module documentation, omitted the unused
noncomputable section and open command, and added the modification notice
and this paired Markdown. Worker 309 supplied the checked closed-target
recipe and confirmed the published target and dependency resolution.

The original 2026 copyright, Apache-2.0 release statement and authorship
header are retained. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are reused without modification. Their SHA-256 values
are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no entry naming this source file.

The approved checking environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation and exact-target
validation use the project Lean service; independent review and Library
integration establish publication.
