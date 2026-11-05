# Abelianness statements for Renard's normalized basis presheaves

Worker 1595. This pair states the presheaf example in Renard A.VI.1 on the
published normalized basis-presheaf category. Both declarations are unproved
Prop-valued definitions; this pair supplies statement coverage only.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
A.VI.1, printed p.261 / one-based PDF p.267, lists abelian-group presheaves on
a topological space among the abelian-category examples and gives the seven
axioms AB0–AB3*. The presheaf convention is II.2.1, printed p.33 / PDF p.39,
from the opening basis paragraph through (II.2.1.1). Both pages were read and
visually checked, and the source fingerprint was verified.

The supplementary correction list for the 2010 edition, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pp.2–3 and 18–19. Those portions do not change the cited
presheaf definition or abelianness assertion. This bounded check of older
errata does not replace the 2026 original.

The declarations are in `Langlands.Sheaf.Renard`, with parameters
`{X : Type u} [TopologicalSpace X] (B : OpenBasis X)`. The universes `u` and
`v` are independent; the original section-group carriers are in `Type v`.
The two bodies are exactly:

| Declaration | Proposition |
| --- | --- |
| `PresheafAbelianStatement.{u,v} B` | `Nonempty (CategoryTheory.Abelian (Presheaf.{u,v} B))` |
| `PresheafAbelianAxiomsStatement.{u,v} B` | `Langlands.Renard.AbelianAxioms (Presheaf.{u,v} B)` |

The first packages existence of Mathlib's data-bearing abelian structure in
`Nonempty`. The second reuses the published source interface: zero-morphism
data are existentially packaged with a zero object, finite products, finite
coproducts, kernels, cokernels, normal monomorphisms and normal epimorphisms.
The existing theorem
`Langlands.Renard.abelianAxioms_iff_nonempty_abelian (Presheaf.{u,v} B)`
identifies the second body with the first. Thus they express the same
mathematical assertion using the two existing interfaces.

Both use the category instance from [BasisPresheaf](BasisPresheaf.md).
Its objects are the actual contravariant functors
`(BasisOpen B)ᵒᵖ ⥤ AddCommGrpCat.{v}` satisfying `IsNormalized`.
The original section groups and restriction homomorphisms remain those
functors' values and maps. Morphisms are their actual natural transformations,
as exposed by `presheafHomEquiv`; identity and composition use the existing
full-subcategory structure. This functor and full-subcategory presentation,
the universe parameters, and the two proposition wrappers are internal
formal packaging of the cited source assertion and conventions.
The source-axiom interface and its correspondence theorem are explained in
[RenardAbelian](../../CategoryTheory/RenardAbelian.md).

The topology and chosen basis are arbitrary, including empty spaces and bases
omitting the empty open. If an empty basis open is present, normalization
requires its section group to be trivial; if absent, the condition is vacuous.
There is no abelianness, source-axiom, normalization-closure, sheafification,
universe-comparison, separation, compactness, total-disconnectedness or
nonemptiness premise.

No instance or proof of either target is constructed here. In particular,
abelianness of the raw functor category alone does not establish these
normalized-category targets. Their exact proofs, sheaf abelianness, and
the separate all-open and chosen-basis category comparisons remain distinct
obligations; this pair does not complete A.VI.1.
