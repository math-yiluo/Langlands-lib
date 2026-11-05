# Integral-model base change on arbitrary coefficient points

This internal comparison starts with a supplied `IntegralModel R K G`, domains
`R` and `A` with specified fraction fields `K` and `L`, compatible algebra
structures on `R → A → L` and `R → K → L`, and their `IsScalarTower` instances.
All rings and fields lie in one arbitrary universe. It uses the existing actual
group schemes and their scheme-morphism point carriers.

`baseChangeSectionsEquiv` identifies sections of the extended model over `A`
with `A`-valued points of the original model over `R`. It composes the existing
rational-section comparison with the inverse of `ringPointBaseChangeEquiv`.
`baseChangeSectionsEquiv_left` says that its underlying morphism is the section
followed by the first projection to the original model.

`genericModelPointEquiv_coefficientPointMap` compares the maps for every section
of the extended model, including sections which do not descend to `R`. Map the
section into the original group's coefficient points with the specified extended
generic isomorphism, then apply `genericModelPointEquiv`. The result is precisely
coefficient change from `A` to `L` of its original-model `A`-point under
`baseChangeSectionsEquiv`. The proof checks underlying scheme morphisms. The
projection formula `baseChangeGenericIso_hom_fst` removes the generic square
comparison; `baseChangeSectionHom_fst` then identifies the result with ordinary
coefficient change. This candidate adds the needed projection formula and its
symbolic pullback lemmas to the companion `BaseChange` pair.

`mem_baseChange_coefficientIntegralPoints_iff` consequently characterizes the
extended model's image subgroup in `G.affinePoints (CommAlgCat.of K L)`. A point
belongs to that subgroup if and only if its original-model generic point lies in
the range of coefficient change from an actual original-model `A`-point. In one
direction the extended section supplies the witness; in the other direction the
inverse section equivalence supplies a section, and injectivity of
`genericModelPointEquiv` proves its image is the given point.

For an `R`-subalgebra `T` of `L`, with the additional instance
`IsFractionRing T L`, `mem_baseChange_subalgebra_coefficientIntegralPoints_iff`
specializes this criterion: membership is equivalent to all original-model
regular functions, restricted through `genericCoordinate`, taking values in `T`
on the original coefficient point. The theorem with suffix `_testSet` replaces
all functions by the fixed finite `integralPointTestSet R M.group.X`. The supplied
model's affineness and locally finite-type property justify that finite set. The
proofs use `IntegralPointCriterion` on the original model and the exact evaluation
identity `genericModelPointEquiv_evaluation`; no new evaluation convention is
introduced.

The provenance is internal, from the supplied model, the actual pullback and
section correspondences, `GenericCoordinates`, `CoefficientPoints`, and
`IntegralPointCriterion`. The arbitrary-point projection extends the previously
established coefficient base-change construction by pullback coherence. These
results require a supplied model and compatible coefficients. They do not
construct arithmetic models, prove an eventual comparison of families, or prove
local maximality, parabolic covering or the integral Iwasawa existence target.
