# Exactness of actual dynamic normalized induction

Worker 117 proves
`Langlands.Aubert.General.DynamicInductionExactnessStatement.{u,uV}` as the
closed theorem `dynamicInductionExactness`. Its binders are exactly those of
`DynamicInductionFiniteLengthStatement`: every nonarchimedean local field,
connected reductive group scheme and cocharacter, the pinned identity-test
`rationalPointTopology`, the given local compactness and nonarchimedean group
instances, and closedness of the actual dynamic unipotent subgroup. The field
universe `u` and representation-carrier universe `uV` are independent.

The conclusion is `SmoothRep.PreservesFiniteLengthShortExact` of the exact
`normalizedInductionFunctor.{u,uV}` in that target. Thus short exact sequences
whose three inputs have finite group-algebra length remain short exact after
induction. This conclusion does not assert finite length of the output objects.
The normalization is the intrinsic half Haar modulus of conjugation on the
unipotent subgroup, evaluated on the entire parabolic, as implemented by the
existing functor.

The continuity helpers apply more generally to any affine, separated group
scheme over a topological commutative ring. The proof realizes the dynamic
parabolic and centralizer as the closed subgroup schemes constructed in
`GroupScheme.Dynamic.AffineRepresentability`. The multiplicative homeomorphisms
of `PointTopology.RepresentedSubgroup` identify their rational points with the
actual subgroup carriers, with the ambient subspace topologies. The
scheme-theoretic limit homomorphism is continuous on rational points.
`Dynamic.limitGroupHom_comp` and the point-homeomorphism identities identify
this continuous map with the actual `Dynamic.limitHom`.
`dynamic_projection_eq_limitHom` then proves continuity of the decomposition
projection. The separate `isClosed_dynamic_parabolic` helper applies the same
closed representative over a Hausdorff topological commutative ring; it does
not require separatedness of the ambient group as an additional premise.

For the exactness theorem, affineness follows from connected reductivity.
`BruhatTits.localField_t2Space` and `rationalPoint_t2Space` give Hausdorffness of
the original group of points. The supplied local compactness and
nonarchimedean group instances give compact-open cofinality through
`compactOpenCofinal_of_nonarchimedean`. Closedness of the actual parabolic and
continuity of its actual projection are the helpers above.
`normalizedInductionFunctor_preservesShortExact` now applies directly. Its
underlying theorem proves injectivity, middle exactness and surjectivity for
all short exact sequences, using smooth induction and the locally constant
half-modulus twist. No separate topological-group instance is added.

This is an internal derivation from the listed constructions and proved
exactness theorem; it introduces no external structural assertion or change
of topology. In particular it assumes no comparison of normalizations,
unimodularity, admissibility, classification, geometric lemma or finite-length
preservation theorem. The separate irreducible-input result is still required
to prove the task's full finite-length target.

The proof imports its published statement and construction dependencies
unchanged. This pair supplies the separate proof of dynamic exactness and its
specialized continuity and closedness helpers.
