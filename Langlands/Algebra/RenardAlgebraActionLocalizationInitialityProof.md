# Initiality of the canonical arrow of the localized algebra action: proof

Authors: Worker 709 wrote the shared Lean draft under whole-book Renard task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 3. Worker 1570 checked the
source passages, the imported objects and the implemented proof, expanded this
English documentation, and prepared the submission under exact proof task
`7973e016-e501-4153-a0e5-6bec84b8598b` revision 1. The Lean proof is unchanged
from the shared draft. The module
`Langlands/Algebra/RenardAlgebraActionLocalizationInitialityProof.lean` proves
the closed statement
`Langlands.Renard.AlgebraActionLocalization.InitialityStatements.{u,v,w,x}`
of [`RenardAlgebraActionLocalizationInitialityStatements`](RenardAlgebraActionLocalizationInitialityStatements.md).
It imports that statement module and the published
[`RenardAlgebraLocalizationUniversalProof`](RenardAlgebraLocalizationUniversalProof.md)
by Workers 1019 and 926. It changes no imported object.

## Source and derived scope

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1570 reread Appendix A.III.1, printed pp.251–252 / one-based PDF257–258,
and the conventions on printed p.6 / PDF12 for this proof.

PDF257 defines the right universal problem for a functor F and an object Y:
an arrow i from Y to F(X) must factor every arrow from Y to F(Z) uniquely
through F. Example 5 on PDF258 applies this to modules with an endomorphism
and targets with invertible endomorphism. Its final sentence says the
construction can be repeated for B-modules and their B-linear endomorphisms.
It gives no separate B-module argument. PDF12 permits nonunital rings and
modules whose action need not preserve a unit. The proof below applies the
published k-linear factor and its proved B-linearity.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF15 and PDF18–19. The PDF15 reference to A.III.1 example 5
corrects a cross-reference elsewhere; these checked pages do not correct the
assertion used here. This bounded older-edition check supplements the governing
2026 original.

As explained in the unchanged statement and definition Markdown, the arbitrary
commutative coefficient ring, the action encoding
`B →ₙₐ[k] Module.End k M`, the actual full subcategory, the structured arrows,
and the universe lifts are internal derived formulations. The field clause
specializes the ring theorem to the source's k-algebra setting. This proof
establishes the three-clause categorical aggregate; it makes no claim about
the other A.III examples or completion of Appendix A.

## Proof route

All declarations are in `Langlands.Renard.AlgebraActionLocalization`. They bind
`k : Type u` with `[CommRing k]` and `B : Type v` with
`[NonUnitalRing B] [Module k B]`. Write a = `endomorphism A`, U for
`raisedFunctor.{u,v,w,x} k B` and J for
`invertibleActionInclusion.{u,v,max u w x} k B`. The carrier of the raised
source is `ULift.{max u x} A.a`. The carrier of `localizedObject A` is
`ULift.{x} (Localized a)`. Both lie in `Type (max u w x)`, while the algebra
universe v remains independent.

1. `baseIntertwiner g` turns a morphism `g : U.obj A ⟶ J.obj T` into the
   actual `LinearIntertwiner A.a.action T.obj.a.action`. It precomposes the
   underlying intertwiner of g with the inverse of `ULift.moduleEquiv`.
   `baseIntertwiner_intertwines g` reads the compatibility of g with the
   endomorphisms through `intertwining_iff`. It gives
   `baseIntertwiner g (a z) = T.obj.str.hom (baseIntertwiner g z)`.
2. `factorIntertwiner A T g` is the published factor
   `EndomorphismLocalization.factor a b hb f` with b the endomorphism of T, hb
   its invertibility `T.property` and f the base intertwiner. Its action law is
   the published `factor_map_localizedAction`, which states that this factor
   intertwines the localized action with the action on T. So it is an actual
   intertwiner from `objectLocalizedAction A` to the action on T.
3. `canonicalFactor A T g : localizedObject A ⟶ T` precomposes that
   intertwiner with `ULift.moduleEquiv` and packs it with `ObjectProperty.homMk`.
   Its compatibility with the endomorphisms is the published
   `factor_intertwines`.
4. `canonicalFactor_fac` proves
   `canonicalArrow A ≫ J.map (canonicalFactor A T g) = g`. After
   `Endofunctor.Algebra.Hom.ext` and `ActionModuleCat.hom_ext`, this is the
   published `factor_comp_iota` at `z.down`.
5. `canonicalFactor_unique` proves that every h with
   `canonicalArrow A ≫ J.map h = g` equals `canonicalFactor A T g`. The
   underlying k-linear map of h, precomposed with the inverse lift, intertwines
   `localizedEnd a` with b. Evaluating the hypothesis at `ULift.up z` shows that
   it agrees with f after `iota a`. The published `factor_unique` then
   identifies it with the factor. Extensionality for `ObjectProperty`,
   `Endofunctor.Algebra` and `ActionModuleCat` morphisms concludes.
6. `canonicalIsUniversal A` builds the initiality data with
   `IsInitial.ofUniqueHom`. A structured arrow g goes to
   `StructuredArrow.homMk (canonicalFactor A g.right g.hom)`, and uniqueness
   comes from `StructuredArrow.ext` and `canonicalFactor_unique`.
7. `factorization` is `IsUniversal.existsUnique` of `canonicalIsUniversal` at
   `StructuredArrow.mk g`. `initiality` wraps `canonicalIsUniversal A` in
   `Nonempty`. `fieldFactorization` applies `factorization`; the extra field
   and algebra hypotheses are not used. `initialityStatements` is the
   conjunction of the three.

The theorem has no outer premises. The general clauses quantify over every
commutative unital ring k, including the zero ring, and B with only
`NonUnitalRing B` and `Module k B`. They add no unit or commutativity assumption
on B, no unit-action or nondegeneracy law, no invertibility assumption on the
source operator, and no dimension, finiteness or `Small` hypothesis. Zero
modules, zero actions and zero or nilpotent source operators are included.
The target's invertibility is precisely its published property
`IsUnit (endomorphism T.obj)`. Uniqueness quantifies over every morphism h in
the actual full subcategory.

`canonicalIsUniversal` constructs data for the published
`canonicalStructuredArrow A` itself. Neither a replacement arrow nor a supplied
universal-property certificate occurs as a premise. The field clause retains
the published `IsScalarTower k B B` and `SMulCommClass k B B` instances; the
general argument does not need them.

## Checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, development check
`7b5e9324-87fe-4cbb-bc89-62635289a6d9` compiled the proof over its unchanged
published imports with zero errors and zero warnings. Inspection of
`initialityStatements` reported a theorem with independent level parameters
u, v, w and x and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The file contains no proof holes or new axioms. Development
compilation does not establish independent acceptance or publication.
