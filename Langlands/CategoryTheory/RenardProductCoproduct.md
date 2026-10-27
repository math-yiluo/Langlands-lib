# Renard A.VI.2(7): proof that binary products and direct sums are naturally isomorphic

Author: Worker 794 (Lean proof and this note). The proved statement and its
specification are the published unit
`Langlands.CategoryTheory.RenardProductCoproductStatements`, written by Worker
721 and Worker 6. This unit imports that module by name and does not change it.
No other proof draft was reused.

## Target

Module `Langlands.CategoryTheory.RenardProductCoproduct` proves

```lean
theorem Langlands.Renard.productCoproductNaturalIso
    (C : Type u) [Category.{v} C] [Abelian C] :
    ProductCoproductNaturalIsoStatement C
```

for an arbitrary abelian category, with independent object universe `u` and Hom
universe `v`. It adds no further hypotheses: no smallness, well-poweredness,
concrete-category, Grothendieck, module or finite-dimensional assumption. Zero
or empty objects are allowed. The binders `(C : Type u) [Category.{v} C]
[Abelian C]` appear in the same order as in the statement.

The original assertion is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.VI.2(7), printed page
262 / PDF page 268 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). For every
pair `(A, B)`, the product `A × B` and the sum `A ⊕ B` are naturally
isomorphic. By A.VI.1 (printed page 261 / PDF page 267), `⊕` denotes the
coproduct. The source gives no proof or explicit map. The statement Markdown
explains how the comparison map, its inverse and matrix normalizations make
the assertion precise. This proof follows the statement's formulation and not
any route from the source.

Notation, as in the statement:

```lean
c(X, Y) := coprod.desc (prod.inl X Y) (prod.inr X Y) : X ⨿ Y ⟶ X ⨯ Y
d(X, Y) := prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr : X ⨯ Y ⟶ X ⨿ Y
```

`X ⨿ Y` and `X ⨯ Y` are the actual chosen coproduct and product supplied by
`Abelian C`. `prod.inl X Y = prod.lift (𝟙 X) 0`,
`prod.inr X Y = prod.lift 0 (𝟙 Y)`, `coprod.fst X Y = coprod.desc (𝟙 X) 0` and
`coprod.snd X Y = coprod.desc 0 (𝟙 Y)` are Mathlib's zero-normalized maps
(`Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean`). The addition in
`d` is the preadditive structure of `Abelian C`.

## Proof method

Every identity is checked directly on the actual coproduct and product. The
proof uses their extensionality lemmas `coprod.hom_ext` (a map out of `X ⨿ Y`
is determined by its composites with `coprod.inl`, `coprod.inr`) and
`prod.hom_ext` (a map into `X ⨯ Y` is determined by its composites with
`prod.fst`, `prod.snd`). Each resulting goal is closed by plain `simp`. The
inverse laws add `Preadditive.comp_add` or `Preadditive.add_comp` to the
`simp` set. Mathlib's chosen biproduct `X ⊞ Y` is never used, so no comparison
between biproduct maps and `c`, `d` is needed.

A `simp?` run in the pinned environment lists the lemmas these `simp` calls
use. They are Mathlib's
- coproduct lemmas: `coprod.desc_comp`, `colimit.ι_desc`, `BinaryCofan.mk_pt`,
  `BinaryCofan.mk_inl`, `BinaryCofan.mk_inr` and `coprod.map_desc`;
- product lemmas: `prod.comp_lift`, `limit.lift_π`, `BinaryFan.mk_pt`,
  `BinaryFan.mk_fst`, `BinaryFan.mk_snd`, `prod.map_fst` and `prod.map_snd`;
- zero-normalized lemmas: `prod.inl_fst`, `prod.inl_snd`, `prod.inr_fst`,
  `prod.inr_snd`, `coprod.inl_fst`, `coprod.inl_snd`, `coprod.inr_fst`,
  `coprod.inr_snd` and their `_assoc` forms;
- general lemmas: `Category.assoc`, `Category.comp_id`, `Category.id_comp`,
  `zero_comp`, `comp_zero`, `add_zero` and `zero_add`.

The submitted proofs call `simp`, not these `simp only` lists.

## Declarations

All declarations are in namespace `Langlands.Renard`. In the first section `C`
is implicit; the five clause theorems at the end take `C` explicitly, like
the statements.

### Matrix entries

- `coprodProdComparison_inl_fst X Y : coprod.inl ≫ c(X, Y) ≫ prod.fst = 𝟙 X`
- `coprodProdComparison_inl_snd X Y : coprod.inl ≫ c(X, Y) ≫ prod.snd = 0`
- `coprodProdComparison_inr_fst X Y : coprod.inr ≫ c(X, Y) ≫ prod.fst = 0`
- `coprodProdComparison_inr_snd X Y : coprod.inr ≫ c(X, Y) ≫ prod.snd = 𝟙 Y`

Each is `simp`. For example, `coprod.desc_comp` moves `prod.fst` inside
the descent, giving `coprod.desc (prod.inl X Y ≫ prod.fst) (prod.inr X Y ≫ prod.fst)`,
which is `coprod.desc (𝟙 X) 0` by `prod.inl_fst` and `prod.inr_fst`.
Precomposing with `coprod.inl` then gives `𝟙 X` (`colimit.ι_desc`). Each
entry also has a `@[reassoc]` variant.

### Product-side description

`coprodProdComparison_eq_prod_lift X Y :
c(X, Y) = prod.lift (coprod.fst X Y) (coprod.snd X Y)`. Both sides are
compared after precomposing with `coprod.inl` or `coprod.inr` and
postcomposing with `prod.fst` or `prod.snd`. All four cases reduce by `simp`
to identities or zeros that agree.

### Inverse laws and isomorphism

- `coprodProdComparison_comp_inv X Y : c(X, Y) ≫ d(X, Y) = 𝟙 (X ⨿ Y)`.
  By `coprod.hom_ext` it suffices to check after `coprod.inl` and
  `coprod.inr`. For `coprod.inl` the left side is
  `prod.inl ≫ (prod.fst ≫ coprod.inl + prod.snd ≫ coprod.inr)`, extracted by
  `coprod.desc_comp` and `colimit.ι_desc`. It becomes
  `𝟙 ≫ coprod.inl + 0 ≫ coprod.inr = coprod.inl` by `Preadditive.comp_add`,
  `prod.inl_fst_assoc`, `prod.inl_snd_assoc`, `zero_comp` and `add_zero`. The
  case of `coprod.inr` is symmetric.
- `coprodProdComparison_inv_comp X Y : d(X, Y) ≫ c(X, Y) = 𝟙 (X ⨯ Y)`.
  By `prod.hom_ext` it suffices to check after `prod.fst` and `prod.snd`.
  `Preadditive.add_comp`, `Category.assoc`, `colimit.ι_desc` and the
  zero-normalized lemmas `prod.inl_fst`, `prod.inr_fst`, `prod.inl_snd`,
  `prod.inr_snd` give
  `prod.fst ≫ 𝟙 + prod.snd ≫ 0 = prod.fst` and
  `prod.fst ≫ 0 + prod.snd ≫ 𝟙 = prod.snd`.
- `isIso_coprodProdComparison X Y : IsIso c(X, Y)`. This is the explicit
  inverse `d(X, Y)` with the two laws above.
- `coprodProdComparisonIsoOf X Y : X ⨿ Y ≅ X ⨯ Y` (a `noncomputable def`, with
  `@[simps]`). Its `hom` is `c(X, Y)`, its `inv` is `d(X, Y)`, and its two
  inverse laws are the two theorems above.

### Joint naturality

`coprodProdComparison_naturality f g :
coprod.map f g ≫ c(X', Y') = c(X, Y) ≫ prod.map f g` for all
`f : X ⟶ X'` and `g : Y ⟶ Y'`. Both sides are checked on the four
injection/projection pairs. For example, after `coprod.inl` and `prod.fst`
both sides are `f`, and after `coprod.inl` and `prod.snd` both are `0`. There
is also a `@[reassoc]` variant.

### Natural isomorphism of curried bifunctors

`coprodProdNatIso : coprod.functor (C := C) ≅ prod.functor` (a `noncomputable
def`) is built with `NatIso.ofComponents` twice. For fixed `X`, the inner
isomorphism `coprod.functor.obj X ≅ prod.functor.obj X` has components
`coprodProdComparisonIsoOf X Y`. Its naturality in `Y` is
`coprodProdComparison_naturality (𝟙 X) g`, because
`(coprod.functor.obj X).map g = coprod.map (𝟙 X) g` and similarly for the
product. The outer naturality in `X` is checked componentwise (`ext Y`) as
`coprodProdComparison_naturality f (𝟙 Y)`, because
`(coprod.functor.map f).app Y = coprod.map f (𝟙 Y)`. Thus the components are
exactly the canonical comparisons and not arbitrary isomorphisms.
`coprodProdNatIso_hom_app_app X Y :
(coprodProdNatIso.hom.app X).app Y = c(X, Y)` holds by `rfl`; it is tagged
`@[simp]`. The inverse components are `(coprodProdNatIso.inv.app X).app Y =
d(X, Y)`, by construction.

### The four clauses and the aggregate

- `coprodProdComparisonIso C : CoprodProdComparisonIsoStatement C`, from
  `isIso_coprodProdComparison`, `coprodProdComparison_comp_inv` and
  `coprodProdComparison_inv_comp`.
- `coprodProdComparisonMatrix C : CoprodProdComparisonMatrixStatement C`, from
  `coprodProdComparison_eq_prod_lift` and the four matrix entries, in the
  statement's order.
- `coprodProdComparisonNaturality C :
  CoprodProdComparisonNaturalityStatement C`, from
  `coprodProdComparison_naturality`.
- `coprodProdNatIsoExists C : CoprodProdNatIsoStatement C`, with witness
  `coprodProdNatIso` and component identity `coprodProdNatIso_hom_app_app`.
- `productCoproductNaturalIso C : ProductCoproductNaturalIsoStatement C`, the
  conjunction of the four, in order.

## Checks and scope

The module imports only `Langlands.CategoryTheory.RenardProductCoproductStatements`.
The `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` built it
with no errors or warnings. It reported the axioms of
`Langlands.Renard.productCoproductNaturalIso` as exactly `propext`,
`Classical.choice` and `Quot.sound`. The file contains no `sorry`, `admit` or
new axioms and does not assume any conclusion.

This unit proves A.VI.2(7) only. The derivation of A.VI.1's seven-axiom
formulation and of the additive Hom groups of A.VI.2(6) is outside this unit.
So are the other A.VI.2 assertions (images, coimages, subobjects, Noether
isomorphisms, the 3-by-3 lemma) and infinitary conventions. Here the additive
structure is the one supplied by Mathlib's `Abelian C`.
