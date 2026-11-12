# Uniform lifts with varying relative dimension

This internal reduction for Conrad's Theorem 5.9 assumes the exact published
proposition `SpaceUniformLangWeilStatement`. It does not prove that estimate or
the final adelic openness theorem.

Let the coefficient ring be Noetherian, with the indicated locally finite-type
spectrum map to the lifted integers. For a smooth map of separated finite-type
algebraic spaces with nonempty geometrically connected fibres, the unit proves
one positive constant giving surjectivity on points over every sufficiently
large finite field with its original coefficient-ring action. No constant
relative dimension hypothesis is imposed.

Finite-type atlases over the Noetherian base are finite-presentation atlases.
`smoothTargetPointDimensions` gives a finite locally constant dimension
function on actual target points. Each occurring clopen dimension restriction
has finite-presentation atlases and an actual chart smooth of that dimension,
by `SmoothDimensionModelGeometry`. Its map inherits separatedness,
quasi-compactness, surjectivity and nonempty geometrically connected fibres.
The target restriction is quasi-separated and finite type.

`OriginalBaseUniformLangWeilLifts.exists_bound` therefore applies the assumed
integer-base estimate to each actual restriction, retaining the original
coefficient action. Choose its positive constants `c_n` before quantifying over
fields and target points. The constant `1 + ∑ n, c_n`, summed over the finite set
of occurring dimensions, is positive and dominates every `c_n`. Its square
therefore dominates every `c_n²`. The numerical positivity lemma gives
surjectivity of every restricted field-point map above this common threshold.
`SmoothDimensionFieldPoints.surjective_fieldPoints_of_restrictions` selects the
unique stratum of each target section and includes a restricted source lift.
The empty-target case is covered by the same empty finite sum and vacuous
surjectivity argument.

`exists_uniform_henselian_surjectivity` applies the published smooth Henselian
lifting theorem to a compatible surjection from a Henselian local coefficient
algebra onto a finite field. The residue-field surjectivity just proved gives
surjectivity on its actual integral points. `pointLifts` chooses these lifts.
The constant is independent of both the finite field and the Henselian algebra.

The provenance is the finite dimension decomposition and its actual affine
charts, the original-base comparison of the exact estimate, finite sums of
positive real constants, and the proved smooth Henselian lifting theorem.
The estimate remains an explicit premise throughout; it must be supplied
unconditionally before this reduction can close the host theorem.
