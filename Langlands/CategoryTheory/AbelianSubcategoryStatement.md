# Corrected abelian full-subcategory criteria and a dimension-one counterexample

Author: Worker 633. This is a statement family, with transparent supporting
definitions and the elementary membership proof needed to construct the actual
line. None of the five substantive result targets is proved here.

## Original source and correction

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.VI.1, printed page 261 /
PDF page 267. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
It remains unchanged as evidence.

The disputed sentence says, in English translation, “Every full subcategory of
A-mod closed under passage to submodules and quotients is still an abelian
category.” No finite-sum or finite-product closure hypothesis appears in that
sentence. The full-subcategory convention at printed page 251 / PDF page 257 is
the fully faithful inclusion convention; it imposes no such closure. The
following AB0 and AB1 at printed page 261 explicitly require a zero object and
finite products. At printed page 262 / PDF page 268, item 7 identifies binary
products and direct sums in an abelian category. These pages were read directly;
PDF page 267 was also visually inspected.

The criteria below are explicitly strengthened sufficient corrections, derived
from Mathlib's construction. They are not verbatim assertions of the book, nor
necessity claims or classifications of all abelian full subcategories. Finite
products in an ambient abelian category are finite direct sums, so the additional
closure supplies precisely the finite-sum condition missing from the source.

The author-page books section in the registered 26 October 2026 snapshot
`renard-author-page-2026-10-26` links the corrected French 2026 version and a
separate errata file explicitly for the 2010 edition. The snapshot has SHA256
`143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`
and is retained at
`/home/taskhub/pilot/literature/David Renard — Author page and 2026-2010 book edition and errata links (snapshot 26 October 2026).html`.
No separate 2026 errata link appears in that books section. The registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its appendix correction portion on PDF pages 18–19 was read directly and does
not repair this sentence. This limited check does not assert an exhaustive
absence of other errata, and the 2010 material does not replace the 2026 edition.

## Declarations and exact mathematical content

Every name below is in namespace `Langlands.CategoryTheory`. The two general
criteria have `C : Type u`, `[Category.{v} C]`, `[Abelian C]` and
`P : CategoryTheory.ObjectProperty C`, with independent object universe `u` and
morphism universe `v`.

| Statement declaration | Content |
| --- | --- |
| `AbelianOfKernelsCokernelsFiniteProducts` | `P.ContainsZero`, `P.IsClosedUnderKernels`, `P.IsClosedUnderCokernels` and `P.IsClosedUnderFiniteProducts` imply `Nonempty (Abelian P.FullSubcategory)`. |
| `AbelianOfSubobjectsQuotientsFiniteProducts` | `P.ContainsZero`, `P.IsClosedUnderSubobjects`, `P.IsClosedUnderQuotients` and `P.IsClosedUnderFiniteProducts` imply the same conclusion. |
| `DimensionLEOneClosedUnderSubobjectsQuotients` | For every field `K`, the actual dimension-at-most-one property contains zero and is closed under all ambient subobjects and quotients. |
| `DimensionLEOneLineHasNoBinaryProduct` | The actual line has no categorical binary product with itself in the dimension-at-most-one full subcategory. |
| `DimensionLEOneNotAbelian` | That full subcategory admits no Mathlib abelian structure. |

All five are transparent `def` declarations returning `Prop`. Mathlib's
`Abelian` contains preadditive data and is not itself a proposition.
`Nonempty (Abelian ...)` expresses existence as a proposition. No abelian
structure on the full subcategory is an input instance. None of the result
targets is assumed as a certificate when defining any other target.

The general hypotheses are Mathlib's actual categorical closure predicates.
`ContainsZero` means that some ambient zero object satisfies the property.
`IsClosedUnderSubobjects` quantifies over every ambient monomorphism `X ⟶ Y`
and asserts `P Y → P X`; `IsClosedUnderQuotients` quantifies over every ambient
epimorphism and asserts `P X → P Y`. They are not restricted to selected linear
subspaces or selected quotient constructions. Kernel and cokernel closure
likewise concern all appropriate universal constructions between property
objects, and finite-product closure uses actual finite discrete diagrams.

## The concrete counterexample

For arbitrary `K : Type u` with `[Field K]`, `dimensionLEOneProperty K` is
the actual object property on `ModuleCat.{u} K` given by

```text
FiniteDimensional K V ∧ Module.finrank K V ≤ 1.
```

The finite-dimensionality conjunct is essential: infinite-dimensional spaces
can have natural-number finrank zero. A bare finrank bound would therefore
define the wrong full subcategory.

`DimensionLEOneModuleCat K` abbreviates precisely
`(dimensionLEOneProperty K).FullSubcategory`, with Mathlib's induced morphisms.
For this concrete witness only, module carriers are in the same universe as
the field. Thus `ModuleCat.of K K` is an available object without a lifted line.
This choice does not restrict the two independent universes of the general
criteria. There is no characteristic assumption on `K`.

`dimensionLEOneLine K` is that actual object `ModuleCat.of K K` bundled into the
full subcategory. Its intrinsic membership uses the existing finite-dimensional
instance for `K` over itself and `Module.finrank_self`; it does not assume a
membership certificate or substitute an arbitrary object.

The no-product target is
`¬ CategoryTheory.Limits.HasBinaryProduct (dimensionLEOneLine K) (dimensionLEOneLine K)`
in this full subcategory. It excludes every object with every pair of possible
projections satisfying the internal universal property. Merely observing that
the ambient space `K × K` has dimension two would not establish this target.
The no-abelian target is independently stated as
`¬ Nonempty (Abelian (DimensionLEOneModuleCat K))`.

The counterexample and strengthened criteria follow the source discrepancy
analysis in the public note `notes/renard/appendix-a-corrections.md`, authored by
Worker 6. Their formal statement formulation here is derived content rather
than an attribution of these corrections to Renard.

## Proposed reuse route and remaining proof obligations

The approved Mathlib environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
`Mathlib.CategoryTheory.Abelian.Subcategory` provides the abelian full-subcategory
instance from zero containment and kernel, cokernel and finite-product closure.
`Mathlib.CategoryTheory.ObjectProperty.Kernels` derives kernel closure from
subobject closure and cokernel closure from quotient closure.
`Mathlib.CategoryTheory.ObjectProperty.EpiMono` supplies the all-monomorphism and
all-epimorphism definitions used in the targets. These are reuse routes for
future proofs; this file does not implement or claim those proofs.

For the concrete closure statements, the proposed route uses
`ModuleCat.mono_iff_injective`, `ModuleCat.epi_iff_surjective`, finite-dimensional
transport and dimension monotonicity. For the no-product statement, a
hypothetical internal product with projections `p, q : V → K` would make the
linear map `V → K × K`, `x ↦ (p x, q x)`, surjective: use the universal property
on every pair of endomorphisms of the actual line taking `1` to prescribed
scalars. The bound on `V` would contradict dimension two of the target. This
excludes any internal product candidate. The proposed no-abelian argument then
uses the finite products required by any abelian structure. These proof routes
remain unimplemented here and need independent proof submissions against the
accepted statement declarations.

The formal example uses existing unital `ModuleCat`. Submodules and quotients
of unital vector spaces remain unital even in the book's larger possibly
nonunital module setting, so the mathematical source discrepancy persists
there. A formal embedding into that pending category is a separate adapter
obligation. Equivalence of the source's AB0–AB3* axioms with Mathlib's definition,
the general possibly nonunital module category, and A.VI.2 and later assertions
are outside this statement family.
