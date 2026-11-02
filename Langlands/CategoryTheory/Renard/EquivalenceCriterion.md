# Renard A.II.2: proof of the equivalence criterion

`Langlands.Renard.equivalenceCriterion` proves the published proposition
`Langlands.Renard.EquivalenceCriterionStatement C D`. For every functor
`F : C ⥤ D`, surjectivity and injectivity of its actual Hom maps and the
existence of an isomorphism from an image object to every target object
produce one reverse functor `G : D ⥤ C` with natural isomorphisms
`F ⋙ G ≅ 𝟭 C` and `G ⋙ F ≅ 𝟭 D`.

## Source and typing convention

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
A.II.1–2, printed pp.250–251 / PDF256–257, supplies natural isomorphisms,
the quasi-inverse definition and the final unnumbered sufficient
criterion. These pages were read, and PDF257 was inspected visually.

The boxed quasi-inverse definition on PDF257 swaps the identity-category
subscripts under conventional composition. Its immediately preceding
strict-inverse paragraph and A.I.1, printed p.247 / PDF253, establish the
intended convention. In Lean's application-order notation, `F ⋙ G` is an
endofunctor of `C` and `G ⋙ F` is an endofunctor of `D`, so the identities
in the theorem have the types displayed above. The proof uses the
published statement unchanged, including this documented correction.

The supplementary registered source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its PDF18–19 appendix corrections were read and contain no correction to
these A.II subscripts. This bounded check of older errata does not replace
the governing 2026 edition.

## Implemented proof

The implementation reuses `Mathlib.CategoryTheory.Equivalence`, imported
by the statement module, at pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
It installs `Functor.Full` from the given Hom-map surjections,
`Functor.Faithful` from the given Hom-map injections, and
`Functor.EssSurj` from the given object-isomorphism witnesses.
Together these give `Functor.IsEquivalence`.

`Functor.asEquivalence` then constructs an actual equivalence. Its inverse
functor chooses an object preimage of each target object and lifts each
morphism through the full functor after conjugating by the chosen object
isomorphisms. Faithfulness supplies the functor laws. The construction
also supplies natural unit and counit isomorphisms.

The proof chooses exactly `F.asEquivalence.inverse` as `G` and returns
`F.asEquivalence.unitIso.symm` and `F.asEquivalence.counitIso` as the two
witnesses. The unit is reversed to obtain `F ⋙ G ≅ 𝟭 C`; the counit already
has type `G ⋙ F ≅ 𝟭 D`. Both use the same inverse functor and are actual
isomorphisms in functor categories. `Nonempty` wraps their existence in
`Prop`.

This is a Mathlib reuse proof of Renard's sufficient criterion. Renard
cites [28], Theorem 1.13, and [25], Theorem 2.3.5, without proving it on
PDF257; the present implementation does not claim to transcribe either
reference's proof.

The four universe parameters `v₁`, `v₂`, `u₁`, `u₂` remain independent.
There is no additional nonemptiness, smallness, additive, abelian or
finiteness assumption, so empty categories are included. The theorem
proves only the published sufficiency direction. The skeleton example,
the general representative-subcategory discussion, a converse criterion
and the other A.I–A.II obligations remain separate.

Implementation: Worker 709; source verification and preparation for
submission: Worker 1158.
