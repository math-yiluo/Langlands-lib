# Full integer-valued normalizer generation from rational root generation

This internal reduction applies to arbitrary-field supplied
`IntegerValuationBuildingData v G`. It introduces
`reflectionRelativeWeylMap`, the actual normalizer quotient projection
`N(k) → N(k)/Z(k)` restricted to `reflectionNormalizer`, and proves it
surjective without an extra hypothesis. The result extends the finite-Weyl
argument of the published local-field module
`ReflectionTranslationLattice`; it uses no translation-lattice assertion.

For each actual relative root, choose a nonidentity root point and an
opposite pair. Its representative belongs to `reflectionNormalizer`,
negates the root and centralizes its full character kernel.
These representatives give the published integral reflection datum.
The actual relative-root-system theorem and its theorem
`closure_representatives_eq_top` make their quotient classes generate the
whole relative Weyl group. Closure in the range proves surjectivity,
including when the root set is empty.

The rank-one containment theorem in
`IntegerRankOneReflectionGeneration` puts every centralizing point of
an opposite-root-generated subgroup into the ambient image of
`reflectionNormalizer`. Passing to subgroup closure gives the same
containment for `RelativeRoot.rankOneCentralizerGeneratedPoints`.
The published arbitrary-field theorem `rootGeneratedCentralizerRankOne`
then puts every centralizer point lying in
`relativeRootGeneratedSubgroup` into that image.

Under the explicit hypothesis
`relativeRootGeneratedSubgroup B.i = ⊤`, this contains the whole
centralizer. For any normalizer point `n`, relative-Weyl surjectivity
supplies a reflection product `r` with the same quotient class. Thus
`r⁻¹ * n` centralizes the torus, so belongs to the reflection subgroup.
Multiplication by `r` proves that `reflectionNormalizer` is the whole
actual normalizer. Its image equality from `IntegerRootReflectionWeyl`
therefore becomes the full normalizer-image equality.

The provenance is the named published Library constructions and the
elementary quotient-group argument just described. The final equality
retains rational root generation as a premise. It is a reduction, and
does not prove that premise or the unconditional simply connected
maximal-unramified target.
