# Derived sections and derived Hom comparison

This is internal comparison infrastructure for relative module cohomology and
the actual Ext-defined cohomology of underlying abelian sheaves. It constructs a
natural comparison on bounded below derived categories, characterized on every
complex by the existing canonical cycle-localization map. This supporting unit
does not prove the relative module/sheaf pullback statement.

The parameters are abelian categories `C`, `D`, and `A`, with chosen derived
categories, enough injectives in `C`, an additive functor `F : C ⥤ D`, an additive
homology-preserving functor `G : D ⥤ AddCommGrpCat`, an exact additive functor
`U : C ⥤ A`, an object `Z : A`, and an isomorphism
`e : F ⋙ G ≅ U ⋙ Hom(Z, -)`. The categories `C` and `A` have the same morphism
universe. An explicit `ULift` on the sections groups accommodates the universe of
the chosen derived category of `A`.

`sectionsComplexIso` is the termwise isomorphism from the complex `G(F(K))` to
`Hom(Z, U(K))` induced by `e`. `sectionsHomologyIso` identifies `G` applied to
degree-`n` cohomology of the localization of `F(K)` with degree-`n` homology of
`Hom(Z, U(K))`. It composes the existing localized homology comparison, the
inverse of the homology-preservation comparison for `G`, and homology of the
termwise isomorphism. The accompanying naturality lemma follows from naturality
of these three maps.

`sectionsCohomology G n` applies homology, `G`, and `ULift` to an object of
`D⁺(D)`. `derivedSections F G n` precomposes this with `RF`.
`derivedHom U Z n` sends an object `L` of `D⁺(C)` to
`Hom_{D(A)}(Z[0], U(L)[n])`. The exactness of `U` supplies its induced functor on
derived categories. `complexHom` expresses this Hom group on actual complexes,
and `derivedHomFactors` identifies the derived and complex models through
localization and its exact-functor factorization isomorphism.

`complexComparison` first removes `ULift`, applies `sectionsHomologyIso`, and
then applies the existing `EquivariantComposite.homologyDerivedMap`. Thus it
uses the canonical map obtained by localizing a shifted chain map representing
a cocycle. It is defined on all bounded below complexes, without an acyclicity
assumption. Its naturality uses the proved chain-map naturality of that canonical
map.

`sectionsUnit` is the right-derived unit for `F`, followed by sections
cohomology. The instance `derivedSections_isRightDerivedFunctor` proves that this
postcomposed unit still has the right-derived universal property: the termwise
sections-cohomology functor is derivable using injective complexes, and its unit
is invertible on such complexes. This uses the existing injective-complex
derivability structure from Mathlib.

`comparison` is the natural transformation from `derivedSections` to
`derivedHom` provided by that universal property, applied to
`complexComparison` followed by the inverse of `derivedHomFactors`.
`comparisonOnComplex` restores the complex model. The identities
`unit_comparisonOnComplex` and `unit_comparisonOnComplex_app` state exactly
that the sections unit followed by this comparison equals the original
`complexComparison` on every complex. They are the universal-property
factorization equation followed by cancellation of the factorization
isomorphism.

The final two lemmas additionally assume enough injectives in `A` and that
`U(I)` is `Hom(Z, -)`-acyclic for every injective object `I` of `C`: all positive
right-derived groups of `Hom(Z, -)` at `U(I)` vanish.
`isIso_complexComparison_on_injectives` uses the existing bijectivity theorem
for `homologyDerivedMap` on bounded below complexes of such acyclic terms.
`isIso_comparison` then proves that the derived comparison is invertible,
first on localizations of injective complexes using the factorization equation,
and then everywhere using their essential surjectivity in `D⁺(C)`.

The provenance is internal: these constructions compare existing canonical
derived-functor and Hom-complex constructions. No separate assertion from
external literature is being transcribed.
