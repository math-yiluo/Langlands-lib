# Renard A.VI.2(7): binary products and direct sums are naturally isomorphic

Authors: Worker 721 and Worker 6. Worker 6 wrote the target specification,
including the exact comparison, inverse and functor formulas, and checked in a
private probe that the proposed types elaborate. Worker 721 checked the
original passage independently and wrote this Lean/Markdown pair. This unit
states A.VI.2(7). Its proof is a separate obligation.

## Original and reading boundary

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix A.VI.2(7), printed page 262 / PDF page 268.
Registered source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

PDF pages 267–268 were read directly, and PDF268 was rendered and checked
visually. The assertion reads:

> — 7. Pour tout couple (A, B) d'objets de 𝒜, le produit A × B et la somme
> A ⊕ B dont l'existence est assurée par les axiomes AB1, AB1\* sont
> naturellement isomorphes.

On PDF267 (printed page 261), A.VI.1 lists the axioms AB0–AB3\*. AB1 and AB1\*
give finite products and coproducts. The paragraph after them says that in
abelian categories one writes "somme directe" and `⊕` for the coproduct. Thus
the source's `A ⊕ B` is the coproduct, written `X ⨿ Y` in Lean. The ambient
category here has Mathlib's actual `Abelian` structure. The separate
seven-axiom construction in `Langlands.CategoryTheory.RenardAbelian`
connects the two conventions; this statement does not duplicate it.
The additive Hom groups of A.VI.2(6), which the inverse formula below uses,
are the groups supplied by `Abelian C` through its preadditive structure.

The source does not name the isomorphism. "Naturellement isomorphes" is
formalized by the canonical comparison map below, its natural isomorphism
of bifunctors, and its inverse and matrix normalizations. The source does not
number or display these normalizations separately. They pin down which
isomorphism is meant; see "Provenance of the normalizations".

Errata check: the registered author-page snapshot
`renard-author-page-2026-10-26` was read. Its books section links the
corrected 2026 French and English versions and gives a separate errata file
only for the 2010 edition. The appendix entries of registered
`renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`),
PDF pages 18–19, were read. None of them corrects the product–coproduct
assertion. That file concerns the 2010 edition; the 2026 text governs
this statement.

## Declarations

Module `Langlands.CategoryTheory.RenardProductCoproductStatements` defines five
transparent `def`s returning `Prop`, in namespace `Langlands.Renard`. Each takes
an arbitrary `C : Type u`, `[Category.{v} C]` and `[Abelian C]`, with
independent object universe `u` and Hom universe `v`. None adds a concrete,
module, finite-dimensional, smallness, well-powered or Grothendieck hypothesis.

All statements use the actual chosen binary coproduct `X ⨿ Y` and product
`X ⨯ Y` and their structure maps `coprod.inl`, `coprod.inr`, `prod.fst` and
`prod.snd`. The instances come from `Abelian C`: finite products and
coproducts, and its preadditive structure. They are not separately chosen
biproduct data. `HasBinaryProduct` and `HasBinaryCoproduct` are propositions,
so `X ⨯ Y` and `X ⨿ Y` do not depend on which path supplies the instances.

Throughout, the **canonical comparison** is

```lean
c(X, Y) := coprod.desc (prod.inl X Y) (prod.inr X Y) : X ⨿ Y ⟶ X ⨯ Y
```

It is written out in full in each declaration rather than introduced as a
separate definition. The product inclusions are Mathlib's zero-normalized maps
`prod.inl X Y = prod.lift (𝟙 X) 0` and `prod.inr X Y = prod.lift 0 (𝟙 Y)`
(`Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean`). The
coproduct projections are `coprod.fst X Y = coprod.desc (𝟙 X) 0` and
`coprod.snd X Y = coprod.desc 0 (𝟙 Y)`. Thus `c(X, Y)` is the map whose
restriction to the summand `X` is `(𝟙, 0)` and to `Y` is `(0, 𝟙)`.

The **inverse formula** is

```lean
d(X, Y) := prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr : X ⨯ Y ⟶ X ⨿ Y
```

using the addition on `X ⨯ Y ⟶ X ⨿ Y` from the preadditive structure of
`Abelian C`. Each declaration writes it with the explicit type ascription
`X ⨯ Y ⟶ X ⨿ Y`.

### `CoprodProdComparisonIsoStatement C`

For all `X Y : C`:

1. `IsIso c(X, Y)`;
2. `c(X, Y) ≫ d(X, Y) = 𝟙 (X ⨿ Y)`;
3. `d(X, Y) ≫ c(X, Y) = 𝟙 (X ⨯ Y)`.

Clauses 2 and 3 are both inverse laws. Together they make `d(X, Y)` the
two-sided inverse of `c(X, Y)`. Clause 1 states explicitly that `c(X, Y)` is an
isomorphism, which is the pointwise content of the source assertion. It also
follows from clauses 2 and 3.

### `CoprodProdComparisonMatrixStatement C`

For all `X Y : C`:

1. `c(X, Y) = prod.lift (coprod.fst X Y) (coprod.snd X Y)`;
2. `coprod.inl ≫ c(X, Y) ≫ prod.fst = 𝟙 X`;
3. `coprod.inl ≫ c(X, Y) ≫ prod.snd = 0`;
4. `coprod.inr ≫ c(X, Y) ≫ prod.fst = 0`;
5. `coprod.inr ≫ c(X, Y) ≫ prod.snd = 𝟙 Y`.

Clause 1 gives the equivalent description of the comparison from the product
side, built from the zero-normalized coproduct projections. Clauses 2–5 are the
four matrix entries: an injection precomposed and a projection postcomposed.
The two matching entries are identities and the two off-diagonal entries are
zero. In clauses 2–5, `≫` associates to the right, so
`coprod.inl ≫ c ≫ prod.fst` means `coprod.inl ≫ (c ≫ prod.fst)`.

### `CoprodProdComparisonNaturalityStatement C`

For all `X Y X' Y' : C`, `f : X ⟶ X'` and `g : Y ⟶ Y'`:

```lean
coprod.map f g ≫ c(X', Y') = c(X, Y) ≫ prod.map f g
```

This is joint naturality in both variables with arbitrary morphisms in each.
Taking `g = 𝟙` or `f = 𝟙` gives naturality in each variable separately.

### `CoprodProdNatIsoStatement C`

```lean
∃ e : coprod.functor (C := C) ≅ prod.functor,
  ∀ X Y : C, (e.hom.app X).app Y = c(X, Y)
```

Here `coprod.functor` and `prod.functor : C ⥤ C ⥤ C` are Mathlib's actual
curried bifunctors (`Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts/BinaryProducts.lean`).
On objects they send `X, Y` to `X ⨿ Y` and `X ⨯ Y`. Their actions on morphisms
are `(F.map f).app Y = coprod.map f (𝟙 Y)` and
`(F.obj X).map g = coprod.map (𝟙 X) g` for the coproduct, and analogously with
`prod.map` for the product. The proposition asserts an isomorphism of
bifunctors whose component at every pair `X, Y` is exactly the canonical
comparison. Separate, unrelated isomorphisms for each pair would not satisfy
it. Since inverses in a category are unique, for every such `e` the component
`(e.inv.app X).app Y` is the inverse of `c(X, Y)`. By the first statement, that
inverse is `d(X, Y)`.

### `ProductCoproductNaturalIsoStatement C`

This is the conjunction of the four propositions above, in that order. It is
the combined proof target for A.VI.2(7).

## Provenance of the normalizations

The source asserts only that the product and the direct sum are naturally
isomorphic. The pointwise isomorphism (`IsIso c(X, Y)`), the naturality square
and the natural isomorphism of the bifunctors `coprod.functor ≅ prod.functor`
with components `c(X, Y)` formalize that sentence. The inverse formula `d`,
both inverse equations, the identity `c = prod.lift (coprod.fst X Y)
(coprod.snd X Y)` and the four matrix entries are derived normalizations, as
the task specification requires. They identify the isomorphism as the standard
comparison determined by the canonical maps, rather than leaving it
unspecified. The naturality square makes the word "naturellement" precise in
both variables at once.

## Scope

The file imports `Mathlib.CategoryTheory.Abelian.Basic` and defines the
propositions only. It adds no axiom, has no proof holes, and does not assume
any of its conclusions. It neither uses nor constrains Mathlib's chosen
biproduct `X ⊞ Y`. A proof may go through `biprod.isoCoprod`,
`biprod.isoProd` or `biprodIso`, but must identify the resulting maps with
`c(X, Y)` and `d(X, Y)` on the actual product and coproduct. Other parts of
the parent task stay separate obligations: the derivation of the additive Hom
groups from the seven axioms, images and coimages, the subobject lattice,
Noether isomorphisms, the 3-by-3 lemma, and infinitary conventions.
