# Initiality of the explicit and chosen endomorphism-localization arrows

Authors: Worker 709 prepared this statement unit under whole-book Renard task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 3. It imports the published
[`RenardEndomorphismLocalizationComparison`](RenardEndomorphismLocalizationComparison.md)
by Worker 1581, which in turn imports the published source unit
[`RenardEndomorphismLocalizationSource`](RenardEndomorphismLocalizationSource.md).
No imported object is changed. There is no proof in this file.

## Source and derived provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, printed
pp.251–252 / one-based PDF257–258. Registered source identifier
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These pages were reread directly on 5 November 2026.

- PDF257 defines a solution (X, i) of the right universal problem posed by a
  functor F and an object Y: for every object Z and every morphism
  f : Y → F(Z) there is a unique g : X → Z with F(g) ∘ i = f.
- Example 5 on PDF258 takes a field k, a k-vector space L and a ∈ End_k(L).
  It asserts that there are a pair (L_a, ã) with ã invertible and a morphism
  ι : (L, a) → (L_a, ã) such that, for every morphism f : (L, a) → (M, b)
  with b invertible, there is a unique f̃ : (L_a, ã) → (M, b) with
  f = f̃ ∘ ι. Morphisms of pairs are the linear maps intertwining the
  endomorphisms. The example adds that the same construction works for
  modules over a k-algebra B.
- The remark on PDF258 says that two solutions are isomorphic by a unique
  isomorphism. Its argument applies uniqueness of factors to the two
  canonical maps.

The following choices are internal derived formulations; the source makes none
of them. The coefficient ring is an arbitrary commutative unital ring R, which
contains the field case. The target category is the published full subcategory
of pairs with invertible endomorphism. The two canonical arrows are the published
structured arrows. Uniqueness of factors is stated both with `∃!` and as
`StructuredArrow` initiality. Carriers are lifted into a common universe. The
B-module sentence is covered when B is commutative, since R-linear maps are then
B-linear maps. A noncommutative B is outside this statement.

## Imported objects

All declarations are in `Langlands.Renard.EndomorphismLocalization.ChosenComparison`.
Each binds `R : Type u` with `[CommRing R]` and an arbitrary
`A : PolynomialEndomorphism.EndomorphismCat.{u,v} R`, that is, an R-module in
`ModuleCat.{v} R` together with a specified endomorphism. The universes u, v
and w are independent. Write κ = max u v w and J for
`invertibleEndomorphismInclusion.{u,κ} R`, the inclusion of the full
subcategory `InvertibleEndomorphismCat.{u,κ} R` of pairs whose endomorphism is
a unit. Every R-linear intertwiner between two invertible pairs is a morphism
of this subcategory.

| Name | Actual object |
| --- | --- |
| `raisedFunctor R` | U: the pair `(ULift.{max u w} A.a, ULift of the endomorphism)` in `EndomorphismCat.{u,κ} R` |
| `explicitFunctor R` | E: the invertible pair `(ULift.{w} (Localized a), localizedEnd a)`, a = `endomorphism R A` |
| `explicitArrow R` | iota: the natural transformation U ⟶ E ⋙ J with components the lifted `iota a` |
| `chosenFunctor R` | F: the published chosen-localization composite through polynomial modules |
| `chosenArrow R` | lambda: the published chosen canonical arrow U ⟶ F ⋙ J |
| `targetComparison R` | alpha: the published natural isomorphism F ≅ E |
| `explicitStructuredArrow R A` | `StructuredArrow.mk (iota.app A)` over J |
| `chosenStructuredArrow R A` | `StructuredArrow.mk (lambda.app A)` over J |

The published equation `chosenArrow_comparison` states
lambda.app A ≫ J.map (alpha.hom.app A) = iota.app A.

## Exact assertions

Each component is a closed `def` with value in `Prop`.

`ExplicitFactorizationStatement` quantifies over R, A, every invertible pair
`B : InvertibleEndomorphismCat.{u,κ} R` and every morphism
`g : U.obj A ⟶ J.obj B` of pairs. It asserts

```text
∃! h : E.obj A ⟶ B, iota.app A ≫ J.map h = g.
```

This is example 5 with (M, b) = B, f = g and f̃ = h, written in the source's
right universal-problem direction: first the canonical arrow, then the image
of the factor.

`ChosenFactorizationStatement` is the same assertion with F.obj A and
lambda.app A in place of E.obj A and iota.app A.

`ExplicitInitialityStatement` asserts, for every R and A,

```text
Nonempty (StructuredArrow.IsUniversal (explicitStructuredArrow R A)).
```

In pinned Mathlib, `StructuredArrow.IsUniversal` is an abbreviation for
initiality data in the category of structured arrows from U.obj A to J. The
`Nonempty` wrapper turns that data into a proposition. Every structured arrow
from U.obj A to J is quantified over, which means every invertible target and
every map out of the raised pair. `ChosenInitialityStatement` is the same
assertion for `chosenStructuredArrow R A`.

`ComparisonUniquenessStatement` asserts, for every R and A, two things:

- every h : F.obj A ⟶ E.obj A with lambda.app A ≫ J.map h = iota.app A equals
  alpha.hom.app A;
- every h : E.obj A ⟶ F.obj A with iota.app A ≫ J.map h = lambda.app A equals
  alpha.inv.app A.

This is the PDF258 uniqueness remark for the two particular canonical arrows.
The uniqueness holds among all morphisms compatible with the arrows, not only
among isomorphisms, which is what the source's argument proves.

`FieldExplicitFactorizationStatement` is `ExplicitFactorizationStatement` for
an arbitrary field `k : Type u` and an arbitrary `A : EndomorphismCat.{u,v} k`.
This is the literal setting of example 5. No finite-dimensionality is assumed.

`InitialityStatements.{u,v,w}` is exactly the conjunction of these six
propositions.

## Scope and universes

All rings are allowed, including the zero ring. All modules and all
endomorphisms are allowed, including zero and nilpotent ones; in those cases the
localization is zero. No intertwiner g is assumed injective, surjective or
invertible. There is no `Small` hypothesis, no finite generation, no dimension
bound and no shrinking of a carrier.

The raw localization `Localized a` has carrier universe max u v. For this
reason the source and the target are raised into κ = max u v w. A target with
carrier in a universe at least max u v is covered by choosing w. A target in a
smaller universe has to be raised explicitly first. The statement does not
identify independent universes or claim that the localization lives in Type v.

## Intended proof and remaining scope

No proof is implemented here. A future proof may obtain the explicit
factorization from the published linear universal property in
`RenardEndomorphismLocalization`: `factor`, `factor_intertwines`,
`factor_comp_iota` and `factor_unique`, transported through the explicit
`ULift` linear equivalences and extensionality of full-subcategory morphisms.
Explicit initiality then sends each structured arrow to its unique factor. The
chosen clauses can be transported along the published isomorphism
`structuredArrowComparison`. Comparison uniqueness follows from initiality, and
the field clause by specialization. These are intended steps only. The published
linear universal property is not an accepted proof of these categorical targets.

The source's equivalence between polynomial modules and pairs is the separately
published `PolynomialEndomorphism.equivalence`, with functors `fromPolynomial`
and `toPolynomial`. These statements use those functors only inside the
imported constructions F and E. The noncommutative B-module variant, the
other A.III examples and the rest of Appendix A remain separate obligations. This statement unit establishes neither
a proof nor section or book completion.
