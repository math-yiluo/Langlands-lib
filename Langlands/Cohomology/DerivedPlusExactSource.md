# Right-derived comparisons along an exact source functor

Let \(T\colon C\to D\) be an additive exact functor between abelian categories. `mapDerivedPlus` is its functor on bounded-below derived categories. The existing exact-image homology comparison shows that the image retains each lower cohomological bound. `mapDerivedPlusFactors` and `mapDerivedPlusSingleIso` identify the map on localized complexes and on singleton complexes.

Let \(E\) be abelian. For additive functors \(F\colon C\to E\) and \(G\colon D\to E\), a natural transformation \(F\to G\circ T\) acts termwise on complexes. Assume \(C\) and \(D\) have enough injectives. Compose the termwise comparison with the right-derived unit of \(G\) on the image complex. The defining universal property of the right-derived functor of \(F\) builds `rightDerivedComparison`, with the compatibility on representatives in `rightDerivedComparison_fac`. `derivedComplexComparison` specializes to coefficient objects in degree zero through the exact singleton comparison. The hypotheses on \(T\) are additivity and exactness.

The construction uses the Library's exact derived homology comparison and Mathlib's right-derived functor as a left Kan extension along localization. It supports geometric restriction of compactly supported sections before passing to derived cohomology.
