# Absolute root vector lines from four structural inputs

This internal module derives the exact published
`AbsoluteRootVectorLineStatement` from four generic structural propositions:
`SolvableProperFixedPointStatement`,
`ProjectiveTorusFixedPointDimensionStatement`,
`SolvableTorusQuotientStatement` and
`DynamicCentralizerReductiveStatement`, all at the same universe `u`. Its
first two theorems retain all four as explicit hypotheses. The final
reduction discharges the projective-dimension input by its published proof
and retains the other three. The module therefore does not prove the absolute
vector-line statement.

`absoluteRootTangent_le_one_of_structuralInputs` first derives two further
inputs from published proofs. The published
`solvableMaximalTorusConjugacy_of_torusQuotient_and_dominationSplitness`,
applied to the quotient hypothesis and the published theorem
`unipotentSplitTorusDomination`, gives
`SolvableMaximalTorusConjugacyStatement`. The published
`algClosedMaximalTorusCentralizer_fromQuotient`, applied to the dynamic
centralizer and quotient hypotheses, gives
`AlgClosedMaximalTorusCentralizerStatement`.

Now let `G` be connected reductive over an algebraically closed field, and let
`t` be a split subtorus that is a maximal torus. For each relative root `α`,
the theorem bounds the dimension of the entire unchanged intrinsic root
tangent by one. `finrank_rootTangent_le_one_of_rankOne` reduces this bound to
connected reductive groups containing the same split torus as a maximal
torus, in which any two actual roots are integrally dependent. It uses the
dynamic centralizer hypothesis for that reduction. In that case,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs` supplies the bound from
the fixed-point, projective-dimension, conjugacy and centralizer statements.
Splitness of the torus comes from the split-subtorus hypothesis. `relativeRoots`
is definitionally the root set used by both helpers. The bound covers every
positive integral multiple weight. It assumes no root reducedness, root
multiplicity, primitive character or smooth character kernel.

`absoluteRootVectorLine_of_structuralInputs` passes this bound to the
published bridge `absoluteRootVectorLine_of_tangentBound`. The bridge combines
the published closed root realization, its nonzero intrinsic tangent, smooth
relative dimension and the perfect-field classification of one-dimensional
unipotent groups. Its conclusion is the unchanged published statement.
It provides a closed representative of the actual intrinsic root functor, with
natural one-dimensional additive coordinates on every test scheme.

`AbsoluteRootVectorLineStructuralReductionStatement` is the proposition that
the three remaining structural statements, in the order fixed points, torus
quotient and dynamic centralizer, imply `AbsoluteRootVectorLineStatement`, all
at universe `u`. The projective-dimension input is not among its hypotheses.
`absoluteRootVectorLineStructuralReduction` proves this implication by
applying `absoluteRootVectorLine_of_structuralInputs` with the published proof
`projectiveTorusFixedPointDimension` of
`ProjectiveTorusFixedPointDimensionStatement`. Proving the implication does
not prove its conclusion.

The provenance is internal composition of published Library theorems; no new
literature claim is made. The host statement's source is J. S. Milne,
*Algebraic Groups* (2022), Definition 21.10 and Theorem 21.11(b),(c). That
proof obtains the additive root group from a rank-one homomorphism from
`SL₂`. The present route instead bounds the root tangent through rank-one
quotient curves and generic centralizers. Proofs of the three remaining
structural propositions are separate obligations, and no published target or
imported file is changed.
