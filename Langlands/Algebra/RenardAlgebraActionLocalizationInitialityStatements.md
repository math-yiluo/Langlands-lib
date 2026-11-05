# Initiality of the canonical arrow of the localized algebra action

Authors: Worker 709 prepared this statement unit under whole-book Renard task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 3. It imports the published
definition unit
[`RenardAlgebraActionLocalizationCategory`](RenardAlgebraActionLocalizationCategory.md),
also by Worker 709. That unit in turn imports the published
[`RenardAlgebraActionLocalization`](RenardAlgebraActionLocalization.md). No
imported object is changed. There is no proof in this file.

## Source and derived provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, printed
pp.251–252 / one-based PDF257–258. Registered source identifier
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 reread these pages directly on 5 November 2026.

- PDF257 defines a solution (X, i) of the right universal problem posed by a
  functor F and an object Y: for every object Z and every morphism
  f : Y → F(Z) there is a unique g : X → Z with F(g) ∘ i = f.
- Example 5 on PDF258 takes a field k, a k-vector space L and a ∈ End_k(L).
  It asserts that there are a pair (L_a, ã) with ã invertible and a morphism
  ι : (L, a) → (L_a, ã) such that, for every morphism f : (L, a) → (M, b)
  with b invertible, there is a unique f̃ : (L_a, ã) → (M, b) with
  f = f̃ ∘ ι. Morphisms of pairs are the linear maps intertwining the
  endomorphisms. The final sentence reads: « Si B est une k-algèbre, on peut
  faire la même construction en remplaçant les k-espaces vectoriels par des
  B-modules, et les endomorphismes d'espaces vectoriels par des endomorphismes
  de B-modules. »
- The conventions on printed p. 6 / PDF p. 12 say that rings are not assumed
  unital unless stated, and that modules over a unital ring are not assumed
  unital.

These statements assert the universal property of that final sentence. The
objects are B-modules with a B-module endomorphism. The morphisms are B-module
maps intertwining the endomorphisms. The target pairs are those whose
endomorphism is invertible.

The following choices are internal derived formulations; the source makes none
of them. They are fixed by the imported definition unit, whose Markdown
explains them. A B-module is a k-module with an actual nonunital action
`B →ₙₐ[k] Module.End k M`. The coefficient ring k is an arbitrary commutative
unital ring, which contains the field case. B needs only
`[NonUnitalRing B] [Module k B]`. Invertibility is invertibility of the
underlying k-linear endomorphism. Carriers are lifted into a common universe.
Uniqueness of the factor is stated both with `∃!` and as `StructuredArrow`
initiality.

## Imported objects

All declarations are in `Langlands.Renard.AlgebraActionLocalization`. Each
binds `k : Type u` with `[CommRing k]`, `B : Type v` with
`[NonUnitalRing B] [Module k B]`, and an arbitrary
`A : ActionEndomorphismCat.{u, v, w} k B`. Such an A is a k-module in `Type w`
with an actual action of B and a specified B-linear endomorphism. The universes
u, v, w and x are independent. Write κ = max u w x.

| Name | Actual object |
| --- | --- |
| `ActionEndomorphismCat.{u, v, κ} k B` | pairs in carrier universe κ; morphisms are the B-linear maps intertwining the endomorphisms |
| `InvertibleActionEndomorphismCat.{u, v, κ} k B` | its full subcategory of pairs whose endomorphism is a unit |
| `invertibleActionInclusion.{u, v, κ} k B` | J: the inclusion of that full subcategory |
| `raisedFunctor.{u, v, w, x} k B` | U: lifts a pair to carrier `ULift.{max u x} A.a` |
| `localizedObject.{u, v, w, x} A` | the invertible pair `(ULift.{x} (Localized a), lifted localizedEnd a)` with the lifted published `localizedAction`, a = `endomorphism A` |
| `canonicalArrow.{u, v, w, x} A` | ι: U.obj A ⟶ J.obj (localizedObject A), the lifted published `iotaIntertwiner` |
| `canonicalStructuredArrow.{u, v, w, x} A` | `StructuredArrow.mk (canonicalArrow A)` over J |

Since J is the inclusion of a full subcategory, every B-linear intertwiner
between two invertible pairs is a morphism of the subcategory.

## Exact assertions

Each component is a closed `def` with value in `Prop`.

`FactorizationStatement` quantifies over k, B, A, every invertible pair
`T : InvertibleActionEndomorphismCat.{u, v, κ} k B` and every morphism
`g : U.obj A ⟶ J.obj T` of pairs. It asserts

```text
∃! h : localizedObject A ⟶ T, canonicalArrow A ≫ J.map h = g.
```

This is example 5 for B-modules with (M, b) = T, f = g and f̃ = h, written in
the source's right universal-problem direction: first the canonical arrow, then
the image of the factor. Here f̃ is a morphism of the full subcategory, so it
is B-linear and intertwines the two endomorphisms.

`InitialityStatement` asserts, for every k, B and A,

```text
Nonempty (StructuredArrow.IsUniversal (canonicalStructuredArrow A)).
```

In pinned Mathlib, `StructuredArrow.IsUniversal` is an abbreviation for
initiality data in the category of structured arrows from U.obj A to J. The
`Nonempty` wrapper turns that data into a proposition. Every structured arrow
from U.obj A to J is quantified over, which means every invertible target and
every map out of the raised pair. This is the PDF257 definition of a solution
of the right universal problem posed by J and U.obj A.

`FieldFactorizationStatement` is `FactorizationStatement` for an arbitrary
field `k : Type u` and a `B : Type v` with
`[NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]`.
These are the Mathlib hypotheses for a possibly nonunital k-algebra, the
literal setting of the final sentence. No finite dimension and no unit on B is
assumed.

`InitialityStatements.{u, v, w, x}` is exactly the conjunction of these three
propositions.

## Scope and universes

All commutative rings are allowed, including the zero ring. B may be any
nonunital ring with a k-module structure, including the zero ring; no unit,
commutativity or nondegeneracy is assumed. All modules, actions and
endomorphisms are allowed, including zero and nilpotent ones; in those cases
the localization is zero. No morphism g is assumed injective, surjective or
invertible. There is no `Small` hypothesis, no finite generation and no
dimension bound.

The published carrier `Localized a` lives in `Type (max u w)`. For this reason
the source and the target are raised into κ = max u w x. A target with carrier
in a universe at least max u w is covered by choosing x. A target in a smaller
universe has to be raised explicitly first. The statement does not identify
independent universes or claim that the localization lives in `Type w`.

## Intended proof and remaining scope

No proof is implemented here. A future proof may take the published factor
`EndomorphismLocalization.factor` of the underlying intertwiner of g, together
with `factor_intertwines`, `factor_comp_iota` and `factor_unique`. The
published `factor_map_localizedAction` shows that this factor is B-linear for
the localized action. Transport through the `ULift` linear equivalences and
extensionality of full-subcategory morphisms then gives the factorization.
Initiality sends each structured arrow to its unique factor, and the field
clause is a specialization. These are intended steps only. The published raw
B-linear universal property is not an accepted proof of these categorical
targets.

The other A.III examples and the rest of Appendix A remain separate
obligations. This statement unit establishes neither a proof nor section or
book completion.
