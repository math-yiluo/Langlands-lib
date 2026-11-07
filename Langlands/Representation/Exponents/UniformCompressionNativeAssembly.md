# Uniform dynamic compression from named global inputs

This internal assembly gives a conditional route to the unchanged
`UniformCompressionStabilizationStatement.{u,v}`. It does not establish any of
its thirteen global input statements or an unconditional proof of that target.

## Exact conditional statement

`UniformCompressionNativeReductionStatement` is the implication from the
following existing Library propositions to the existing uniform endpoint:

1. `GenericMinimalParabolicStatement`;
2. `ParabolicDynamicStatement`;
3. `SmoothMaximalSplitTorusConjugacyStatement`;
4. `StandardCocharacterStatement`;
5. `StandardLeviIntersectionStatement`;
6. `RelativeRootSystemStatement`;
7. `DynamicParabolicQuotientCompactStatement`;
8. `RationalPointsIrreducibleAdmissibleStatement`;
9. `RationalSupercuspidalJacquetFamilyFiniteStatement`;
10. `RationalCuspidalInertiaProductDecompositionStatement`;
11. `RationalCuspidalInertiaFinitenessStatement`;
12. `RationalUniversalSmallProgeneratorStatement`;
13. `RationalCuspidalInducedEmbeddingStatement`.

The structural inputs have field universe `u`. The six representation inputs
are instantiated at `{u,max u v}`. The conclusion has the original independent
universes `{u,v}`. The implication retains the input propositions themselves;
it does not replace an unknown compression conclusion with a renamed premise.

## Implemented assembly

`uniformCompressionStabilization_of_nativeStatements` first uses the existing
equivalence between uniform stabilization and eventual stability for each
smooth object. For the group of the target it chooses an actual maximal split
torus and a generic cocharacter using the proved existence theorem, obtains the
actual root system from the named root-system input, and constructs the
standard semidirect decompositions. Closedness of all standard radicals and
Levis and Hausdorffness of the actual point group are proved Library results.

The finite embedding input and the existing
`pointwiseCompressionEventuallyStable_of_cuspidalInduced` reduce the argument
to the actual normalized induction of every cuspidal object on each literal
standard Levi. That reduction embeds an arbitrary object and then its cokernel
into finite sums of cuspidal inductions and uses left exact compression
stability. No finiteness or admissibility assumption on the original smooth
object is added.

For each standard index, `standardCompressionRootPresentation` supplies an
actual root presentation on exactly the canonical standard parabolic and Levi
maps. The geometric standard-representative theorem gives the reductive Levi
and the geometric radical. Its rational points receive their canonical
topology, local compactness, nonarchimedean structure and Hausdorffness from
the existing affine rational-point results.

The intrinsic standard-Levi torus is maximal, and the proved `dynamicLie`
combined with standard families gives its genericity. The ambient actual root
system is inherited by this torus. These same data instantiate the three
global cuspidal inputs: inertia-product decomposition, fixed-level finiteness
of classes, and the small-progenerator property for the full norm-kernel
compact induction. Thus all three are used on the exact rational Levi that
appears in the induction.

`standardCompression_nativeJacquetInputs_of_statements` supplies the native
Jacquet bundle from the two named admissibility and universal-Jacquet
statements. The standard projection is continuous by the proved canonical
projection theorem. The named dynamic quotient-compactness input supplies
compactness of the exact standard parabolic quotient. The existing
`literalLeviInduction_eventuallyStable_of_nativeJacquet` then gives the required
stability, retaining the exact dynamic output cocharacter, compact open
subgroup, contraction element and centrality hypothesis.

Finally, the uniform/pointwise equivalence applies the countable direct-sum
diagonal argument. It chooses one exponent before every representation on a
carrier in `Type v`. Its conclusion is exactly the original pair of stationary
power-range and power-kernel equalities together with complementarity, with
the original dynamic-parabolic and central contraction hypotheses.
`uniformCompressionNativeReduction` records this conditional implication.

## Provenance and scope

This is an internal composition of the named Library reductions and actual
canonical-standard geometry. It introduces no additional literature claim.
The complete proof of the unrestricted uniform endpoint still requires proofs
of the listed global inputs, with independent acceptance and publication.
