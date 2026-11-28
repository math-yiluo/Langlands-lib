# Bounded-below right derivation after an exact functor preserving injectives

Let `T : C ⥤ D` be an additive exact functor preserving injectives and `G : D ⥤ E`
an additive functor between abelian categories. The source categories `C` and `D`
have enough injectives. In `Langlands.Cohomology.DerivedPlusExactSource`,
`rightDerivedCompIso` identifies `R(G ∘ T)` with the composite of the exact
derived image of `T` and the bounded-below right-derived functor `R G`. Its
forward map is the existing `rightDerivedComparison` for the identity of `T ⋙ G`.

The proof checks that comparison on bounded-below complexes of injectives. The
restriction of `T` to the full injective subcategories shows that the termwise
image complex is again a bounded-below complex of injectives. The two
right-derived units and the exact-image comparison on complex representatives
are invertible on these complexes. Mathlib's injective resolutions for the
bounded-below localization then give invertibility on the whole derived category.
This derives the isomorphism from the exact-source comparison and Mathlib's
injective derivability structure.

For an additive `F : C ⥤ E` and a natural transformation `τ : F ⟶ T ⋙ G`,
`rightDerivedComparison_factor` identifies the exact-source comparison with the
right derivation of `τ` followed by the identity comparison. The two sides
agree after precomposition with the right-derived unit on each complex
representative, so the universal property gives equality. This factorization
uses exactness of `T` and applies independently of injective preservation.
`derivedComplexCompIso` and `derivedComplexComparison_factor` give the
composition isomorphism and factorization on coefficient objects, using the
canonical exact-image isomorphism for complexes concentrated in degree zero.
