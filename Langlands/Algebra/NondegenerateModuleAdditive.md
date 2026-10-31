# Additive restriction and the actual nondegenerate-part functor

Authors: Workers 6 and 490. Worker 6 supplied the shared construction draft;
Worker 490 checked its source correspondence and complete interfaces and
prepared the paired submission.

This construction uses the original `NonUnitalModuleHom` pointwise additive
groups and `NonUnitalModuleCat.preadditive` from the published
`Langlands.Algebra.NonUnitalModuleAdditive`. The actual
`NondegenerateModuleCat` is the published full subcategory, with
`Preadditive.fullSubcategory (nondegenerateProperty A)` as its inherited
preadditive structure. The module defines no replacement category, functor
or preadditive structure.

For an arbitrary nonunital ring `A` and `hA : IsIdempotented A`,
`NonUnitalModuleHom.restrictNondegeneratePartAddHom hA` bundles the existing
restriction of an original additive intertwiner to the actual nondegenerate
parts as an additive homomorphism on Hom groups. The zero, addition and
negation lemmas evaluate the maps on each vector and apply subtype
extensionality. The underlying function is definitionally the published
`restrictNondegeneratePart hA`, as the named application and function
equalities state. The ring, source carrier and target carrier have three
independent universes `uA,uM,uN`.

`nondegenerateInclusion_additive` reuses Mathlib's additive inclusion of any
full subcategory with the inherited Hom groups. It needs no idempotentedness
hypothesis. `nondegeneratePartFunctor_additive` is an instance for the actual
published part functor: full-subcategory morphism extensionality reduces its
addition law to the restriction addition law. The named Hom-map equation
identifies its underlying original map with the same restriction. Its zero,
addition and negation laws follow from the additive instance. The actual
ambient composite with `nondegenerateInclusion A` is additive by Mathlib's
composition instance, and a named certificate records this consequence.
These categorical interfaces have independent ring and carrier universes.
Full unapplied interfaces check the Hom construction and its function
equality at arbitrary independent triples, and all three functor
certificates at arbitrary universes and both unequal pairs `(0,1)` and
`(1,0)`. A final instance check uses the actual ambient composite. Additional private
checks assign all thirteen complete unapplied interfaces at arbitrary
independent universes and at unequal universe specializations: all three
functor certificates and four map laws use `(0,1)` and `(1,0)`, and the six
unbundled restriction interfaces use `(0,1,2)` and `(1,0,2)`. Instance checks
for each functor and the composite, and definitional equalities identifying
the inferred full-subcategory preadditive structure, also compile.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original module and Hom conventions are printed pp.5–6/PDF11–12.
I.1.2, printed p.7/PDF13, defines the nondegenerate full subcategory and
largest nondegenerate part; printed p.8/PDF14 describes the functor on
arrows by restriction. A.VI.2 property 6, printed p.262/PDF268, describes
the Hom addition. These additive certificates and the bundled Hom map are
internal consequences of those constructions, rather than separately
numbered assertions of the book. The proofs use the already established
pointwise Hom operations and the actual subtype restriction.

There is no unit-action, nontriviality, commutativity, field, dimension or
finiteness hypothesis. Zero rings, zero carriers and zero actions, including
zero actions over unital rings, are allowed. No closure, abelian or exactness certificate is an
input. The nondegenerate abelian structure, exactness, adjunctions,
completion and complex scalar comparisons are separate obligations.
