# Étale monomorphisms are open immersions

The theorem `Langlands.Analytic.SaturatedAtlasPresentation.openImmersion_of_etale_of_mono`
states: assume `EtaleHomSheafStatement.{u, u}` (for every complete ultrametric normed field
`K` and analytic spaces `X`, `T` of `LocalizedCategory.{u, u, u}`, the presheaf
`U ↦ (U ⟶ T)` on the small étale site of `X` is a sheaf). Then every étale monomorphism
`f : S ⟶ T` of analytic spaces is an open immersion (`openImmersion`): an isomorphism onto
the analytic space of an open subset of `T` followed by its canonical morphism.

## Proof

The image `U` of `f` on underlying points is open because étale morphisms are open
(`etaleOpenMap`). Let `D` be the open domain of `T` on `U` and `f' : S ⟶ D` the factorization
of `f` through `D` (`domainLift`). Then `f'` is étale (`etale_of_comp_domainι`), a
monomorphism, and surjective on points. The single étale morphism `f'` covers `D`. The
identity of `S` is compatible on this cover: for `a, b : V ⟶ S` with `a ≫ f' = b ≫ f'`,
`a = b` because `f'` is a monomorphism. The sheaf property with target `S`
(`exists_glue_of_etale_cover`) gives `g : D ⟶ S` with `f' ≫ g = 𝟙 S`. Then `g ≫ f'` and
`𝟙 D` agree after `f'`, so they are equal by the sheaf property with target `D`
(`hom_ext_of_etale_cover`). Hence `f'` is an isomorphism and `f = f' ≫ domainι T D` is an
open immersion.

## Provenance

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009), p.21, end of
the proof of Lemma 4.2.3 (`conrad-temkin-2009-nonarchimedean-analytification`), identifies
`R → U ×_X U` as an isomorphism by its being an étale monomorphism surjective on geometric
points. The general result here follows by factoring through the open image and descending
the identity along the resulting cover. The hypothesis `EtaleHomSheafStatement` provides
this descent (Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §4.1,
`berkovich-1993-etale-cohomology`, and Conrad–Temkin 2009, Theorem 4.1.2).
