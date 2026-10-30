# Renard A.IX: support and maximality of the actual supported sum

Author: Worker 199.

This module proves the unchanged public
`Langlands.Renard.SimpleSupportSumStatement`. Its two named components
establish support of the actual coproduct-image sum of all supported
subobjects, and its resulting greatest-element property. All declarations
are in namespace `Langlands.Renard`.

The three complete closing types are:

```lean
simpleSupportSumSupport.{w,u,v} :
  (C : Type u) → [Category.{v} C] → [Abelian C] →
    SimpleSupportSumSupportStatement.{w} C

simpleSupportSumMaximum.{w,u,v} :
  (C : Type u) → [Category.{v} C] → [Abelian C] →
    SimpleSupportSumMaximumStatement.{w} C

simpleSupportSumStatement.{w,u,v} :
  (C : Type u) → [Category.{v} C] → [Abelian C] →
    SimpleSupportSumStatement.{w} C
```

The aggregate is exactly the conjunction of the two component propositions.
Each component retains `hG : IsSourceGrothendieck.{w} C`, the derived local
instance `HasCoproducts.{w} C := hG.1`, `SourceAB6 C`, a set
`S : Set (ObjectClass C)` with `S ⊆ simpleClasses C`, and every `X : C`
with `[Small.{w} (simpleSupportSubobjects S X)]`. The public
`hasCoproductsOfShape_of_small.{w}` adapter supplies the coproduct of this
full subtype. There is no other smallness binder.

## Source and provenance

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix A.IX,
printed page 268 / PDF274. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; retained file:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`;
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 199 read original PDF269–270 and PDF273–275 in full and visually
checked PDF274. Renard defines `E_S` as the sum of all subobjects of `E`
belonging to the supported full subcategory `M_S`, and asserts that
`E_S` belongs to `M_S`. This is the source support conclusion proved here.
The greatest-element formulation is an internal order-theoretic consequence.

The proof uses the arbitrary-sum identity of A.VI.3, unnumbered Lemma (iii),
printed page 264 / PDF270, through the published theorem
`simpleSubquotientSum` in
`Langlands.CategoryTheory.Renard.SimpleSubquotientSum`. That theorem is
proved under the same source Grothendieck and source AB6 assumptions, with
an independent family universe `w`. This module derives support from the
proved identity; the identity is not an additional premise.

The complete public Appendix A discrepancy note was read; it addresses
other passages. No dedicated 2026 errata note was found at the checked
workspace, project or Library paths. The supplementary registered
`renard-2010-corrections-complements`, retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. Its old-page310 letter correction replaces
`M, M_S` by `E, E_S`; the governing 2026 text already incorporates it.
This comparison is limited to the inspected pages of a different edition.

## Equality of the actual sums

`simpleSupportSum_eq_subobjectSum_shrink` is an internal derived helper.
It takes `[HasCoproducts.{w} C]` and the one-family smallness instance.
Write `T := simpleSupportSubobjects S X`, `e := equivShrink.{w} T`,
and define

```lean
F : Shrink.{w} T → Subobject X := fun i => (e.symm i : Subobject X)
```

The helper proves `simpleSupportSum S X = subobjectSum F` as an equality
of actual subobjects of `X`. For the forward inequality, every supported
`P` occurs as `F (e ⟨P, hP⟩)`, so `le_subobjectSum` makes the reindexed
sum an upper bound of the whole original family. Apply
`simpleSupportSum_le`. For the reverse inequality, every `e.symm i`
has the support property by its subtype field, so `le_simpleSupportSum`
bounds every `F i`; apply `subobjectSum_le`.

This proves that reindexing gives the public sum itself. It does not
choose a smaller subfamily, identify coproduct choices, or infer support
from the least-upper-bound law.

## Support and maximum

`simpleSupportSumSupport` installs the exact two local coproduct
instances from the published target. The helper rewrites the actual sum
as the `Shrink.{w}`-indexed sum. The published arbitrary-sum theorem
then rewrites its simple-subquotient classes as
`⋃ i, simpleSubquotientClasses (F i : C)`. Every member of this union
belongs to `S` because `(e.symm i).property` is precisely that summand's
support condition. This proves
`HasSimpleSupport S (simpleSupportSum S X : C)`.
The proof retains the source restriction `S ⊆ simpleClasses C` in its
type, although this last subset argument does not need it.

`simpleSupportSumMaximum` pairs this genuine support membership with
`le_simpleSupportSum S X` for every supported subobject. These are
exactly the two fields of
`IsGreatest (simpleSupportSubobjects S X) (simpleSupportSum S X)`.
`simpleSupportSumStatement` pairs the two complete component theorems.

The object, Hom and family universes `u`, `v`, `w` remain independent.
The proof assumes no coproducts at `max u v`, well-poweredness,
local smallness, concreteness, generator, separator, finite length or
finite dimension. It uses the full actual supported-subobject subtype
and the unchanged public coproduct-image construction.

## Reused work and scope

The unchanged support predicate and supported-subobject family were
authored by Workers 6 and 695. The public sum construction was authored
by Worker 985, specified by Worker 6; its universe explanation was
corrected by Workers 6 and 199. The unchanged target statements are by
Workers 6 and 985. The arbitrary-sum proof is by Worker 695, with source
and interface audit and documentation by Worker 595. Its published
dependencies include the clause (i) proof by Worker 695 and the
zero-detection proof by Worker 595. These results and their unchanged
underlying public constructions are reused by Lean name. Worker 199
authored the reindexing helper and this support/maximum assembly.

This module proves support and greatest-element maximality of `E_S`.
Closure and abelianness of `M_S`, Hom orthogonality, disjointness,
splitting and the equivalence with a product of categories remain
separate obligations.

The approved Lean service compiled the proof with zero errors and
warnings and inspected the aggregate theorem with independent level
parameters `w, u, v` and only `propext`, `Classical.choice` and
`Quot.sound`. A separate private diagnostic also printed all four complete unapplied
types and axiom sets, assigned the three closing constants directly to
their named propositions, and assigned the two component constants to
the expanded telescopes with both local instances unchanged. All checks
passed with zero errors and warnings. These development checks are
separate from exact-target validation, independent semantic review and
publication.
