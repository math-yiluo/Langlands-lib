# Full root tangent bounds from rank-one quotient curves

This internal construction extracts a bound on the entire intrinsic root
tangent from the published rank-one quotient-curve data. It is stronger than
positive-root uniqueness because it also bounds root multiplicity. The four
generic geometric inputs in the final conditional theorem remain unproved
hypotheses here.

For any smooth affine group and split torus action by conjugation,
`RelativeRoot.tangentSubmodule_subgroup_le_unipotent` uses the exact published
`tangentSubmodule_subgroup` identification with the positive cyclic weight span.
If a character is positive on a cocharacter, each positive integral multiple
is also positive. The published
`weightSpace_le_tangentSubmodule_unipotent` therefore includes the whole cyclic
span in the dynamic unipotent tangent. `rootTangentToUnipotent` is this linear
inclusion, retaining the original vector.

For a prescribed exact smooth quotient curve of a proper closed solvable
subgroup in semisimple rank one,
`finrank_rootTangent_le_one_of_rankOne_curve` constructs the published
`regularSignedCurveUnipotentDataOfIsConnectedReductive`. The curve data bounds
one of the two signed dynamic tangent dimensions. The published normalizer
conjugacy identifies their dimensions, so the positive one is also at most one.
Regular refinement and normalizer symmetrization preserve the positivity of the
original root. The inclusion above then bounds the full intrinsic root tangent,
without any assumption on root reducedness or on the multiplicity of its
first weight space.

`finrank_rootTangent_le_one_of_prescribedBorel` uses the published
`prescribedBorelProjectiveCurveData` to construct the actual quotient curve.
It also constructs the nonidentity normalizer class by
`nonidentityNormalizerOfRootedSolvableQuotient`, and chooses a cocharacter
positive on the specified nonzero root by split-torus duality.

`rankOne_rootTangent_le_one_of_projectiveBorelInputs` constructs a proper Borel
containing the original torus. The existence of the specified ambient root
establishes that this Borel is proper. It obtains internal Borel-torus
conjugacy from `SolvableMaximalTorusConjugacyStatement`, and all-test
torus-centralizer containment from `AlgClosedMaximalTorusCentralizerStatement`.
Together with `SolvableProperFixedPointStatement` and
`ProjectiveTorusFixedPointDimensionStatement`, these are explicit hypotheses.
The theorem works over every algebraically closed field in every universe and
in arbitrary characteristic, under pairwise dependence of the actual roots.
It does not prove the general root bound or the exact absolute vector-line
target.

The provenance is internal. The proof combines the named published Library
constructions with positivity of positive integral multiples and monotonicity
of finite-dimensional subspace dimension. It introduces no external
mathematical input. The intrinsic root functor and all published statement
pairs are unchanged.
