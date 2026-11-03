# Renard A.II.2: proof of equivalence with selected representatives

`Langlands.Renard.representativeSubcategoryEquivalence` proves exactly the
published `Langlands.Renard.RepresentativeSubcategoryEquivalenceStatement C`.
Worker 1158 adopted Worker 709's complete shared proof implementation, with
Worker 709 retained as coauthor. The published construction, statement and
criterion are imported by Lean name and left unchanged.

## Source and actual construction

The source target is the representative-subcategory discussion at A.II.2,
printed pp.250–251 / one-based PDF256–257 of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These original pages were read, including visual inspection of PDF257.
Renard chooses one object from each isomorphism class and keeps all ambient
morphisms between selected objects. The comparison here makes that introductory
assertion precise using the source's final sufficient criterion on PDF257.

The imported [construction](RepresentativeSubcategory.md) defines
`representativeObjects C` as the actual range of the object map of Mathlib's
`fromSkeleton C`; it then takes the actual full subcategory on that range.
The inclusion `representativeInclusion C` sends objects and morphisms to their
ambient objects and morphisms. In particular, the theorem compares this
constructed category with `C`.

The source's boxed quasi-inverse definition exchanges the identity-category
subscripts. A.I.1, printed p.247 / PDF253, and the strict-inverse paragraph
on PDF257 confirm the composition convention; these passages were read.
For the actual inclusion `ι : RepresentativeSubcategory C ⥤ C`, the correctly
typed natural isomorphisms, in Lean's composition order, are

```text
ι ⋙ G ≅ 𝟭 (RepresentativeSubcategory C),     G ⋙ ι ≅ 𝟭 C.
```

This retains the correction documented in the
[statement companion](RepresentativeSubcategoryStatements.md).
No source-specific Renard errata note was found in the current published
or project `notes/errata` locations. The registered older supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF18–19 for appendix corrections; these pages contain no
correction of the identity subscripts. This bounded supplemental check does
not replace the governing 2026 source.

## Implemented proof

Apply the published `Langlands.Renard.equivalenceCriterion` to the actual
`representativeInclusion C`, with source `RepresentativeSubcategory C` and
target `C`. Its three hypotheses are discharged as follows:

1. For any two selected objects, the actual inclusion's `map_surjective`
   proves surjectivity of the Hom map. This comes from Mathlib's
   `ObjectProperty.full_ι` instance for a full subcategory.
2. For the same actual Hom maps, `map_injective` proves injectivity, from
   `ObjectProperty.faithful_ι`.
3. For every ambient object `X`, choose the object `representativeOf X`
   and the actual isomorphism `representativeIso X` from its included
   representative to `X`. These are supplied by the published construction
   from the skeleton class of `X`.

The criterion supplies one actual reverse functor and both actual
functor-category isomorphisms. Its implemented proof reuses Mathlib's
`Functor.asEquivalence` at pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`, taking the reverse functor
`F.asEquivalence.inverse`, with `unitIso.symm` and `counitIso` for that same
functor. Thus naturality and both inverse laws come from the published
general proof; the present proof uses the objectwise isomorphisms only to
discharge its essential-surjectivity hypothesis.

## Scope

The theorem preserves independent object and Hom universes `u` and `v`
for `C : Type u` with `[Category.{v} C]`. It adds no nonemptiness,
smallness, finiteness or structural premise and includes the empty category.
The single existentially bound reverse functor witnesses both `Nonempty`
natural-isomorphism conclusions. Its object function is not prescribed.

No uniqueness result for quasi-inverses, strict inverse, universe shrinking,
fixed-dimension vector-space comparison or section completion is asserted.
