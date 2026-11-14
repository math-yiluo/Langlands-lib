# The maximal-unramified normalizer image from quasi-split root generation

This internal reduction states and proves
`MaximalUnramified.SimplyConnectedNormalizerAffineWeylReductionStatement`
at arbitrary universe `u`. Its sole premise is the arbitrary-field proposition
`Langlands.GroupScheme.QuasiSplitSimplyConnectedRootGenerationStatement`.
Its conclusion is the unchanged full
`MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement`.
The root-generation proposition remains unproved by this module, so the
reduction supplies no unconditional proof of that conclusion.

The implementation introduces the original nonarchimedean local field `F`,
an arbitrary simply connected affine group `G` over the actual inertia fixed
field `K = LocalGalois.Separable.inertiaFixedField F`, and every supplied
`C : MaximalUnramified.BuildingData F G`. The datum provides connected
reductivity and its maximal split torus. The proved theorem
`Langlands.GroupScheme.henselianDiscreteQuasiSplit` applies to `K` using
`MaximalUnramified.valuation F`, its surjectivity, Henselian valuation subring
and algebraically closed residue field. This proves quasi-splitness of this
particular `G`; no descent of `G` to `F` is required.

The explicit premise now gives
`relativeRootGeneratedSubgroup C.i = ⊤`. The full integer-valued normalizer
image theorem in `IntegerReflectionNormalizerGeneration` applies to that
equality and the same supplied datum. Its conclusion concerns the original
normalizer action and the actual affine roots, exactly as required. All
quantifiers, including arbitrary universe and rank zero, are retained.

The provenance is composition of these Library statements, the proved generic
Henselian theorem and its existing arithmetic specialization adapters, and the
integer reflection-normalizer construction. This is an internal proof route;
it does not transcribe a new assertion from the literature or discharge the
remaining algebraic root-generation premise.
