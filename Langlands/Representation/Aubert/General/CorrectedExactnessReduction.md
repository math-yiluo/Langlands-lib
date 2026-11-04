# Conditional assembly of corrected exactness on the actual complex

Authors: Workers 691 and 1252. This is an internal consequence of the published
`SharpSupportRetentionReduction`, `JacquetExactness` and
`CorrectedGradedExactness` APIs. Worker 1252 authored the last module, which
is imported by its Library name. This module makes no new assertion from the literature.
Its intended application is the corrected full smooth Aubert Theorem 3.6.

All declarations are in `Langlands.Aubert.General.JacquetComplex`. The
index type `ι` is finite and linearly ordered, and `G` is locally compact
and nonarchimedean. The subgroup families `P`, `M`, `U`, their semidirect
decompositions, closedness, modulus and monotonicity data, the inside-Levi
decompositions, and the association predicate are arbitrary.
The three universes `uI`, `uG`, `uV` are independent. The input representation
has carrier universe `max uI uG uV`; the support targets and the actual
complex are used with representation parameter `max uI uV`. This ensures
that the finite product defining each homogeneous object has the same
carrier universe as its coordinates.

`CorrectedExactnessInputs` is a data type bundling the eight structural
premises listed below for fixed families, association predicate, subgroup
`T` and finite point Coxeter system `cs`. Its fields are `gradedVanishing`,
`gradedTransition`, `leviWeyl`, `associationCard`, `associationSupport`,
`bruhatCover`, `inductionJacquet` and `exactnessDetection`, with exactly
the types of the corresponding premises of
`isExactBeforeTerminal_of_correctedTargets`. It is an internal interface
for assembling the actual rational-point data. Declaring this type does
not construct a value of any field.

`degreeObject_isInSupportCategory` assumes
`SupportCategoryInductionJacquetTarget` at this universe and an actual
smooth `A` in `Alg({I})`. It proves that every actual homogeneous object
`StandardComplex.degreeObject ... A k` lies in `Alg({I})`, for every natural
degree `k`. The proof uses the published coordinate intertwiners
`StandardComplex.degreeProjection`, their joint injectivity, and finite
jointly injective support closure
`IsInSupportCategory.of_jointlyInjective`. Each coordinate has the form
`i_{S \ s} r_{S \ s}(A)`, so its support membership follows from the
assumed induction--Jacquet stability. This does not prove stability itself.

`isExactBeforeTerminal_of_correctedTargets` additionally takes an actual
finite relative Weyl quotient for a subgroup `T` and a Coxeter system `cs`.
It assumes:

- the exact `CorrectedGradedVanishingTarget` and
  `CorrectedGradedTransitionTarget`;
- `actualLeviWeylIdentification T M cs`;
- preservation of subset cardinality by every association with conjugate
  Levi, in the direction `J.card = I.card`;
- `SupportCategoryAssociationInvarianceTarget`;
- the cover `IsBruhatCover T (P ∅) (P J)` for every `J`;
- `SupportCategoryInductionJacquetTarget`;
- `SupportCategoryExactnessDetectionTarget`.

For every smooth `A` in `Alg({I})` it concludes the literal
`StandardComplex.IsExactBeforeTerminal ... A I`. The proof transports
support membership to every associated `J` with conjugate Levi, applies
the two associated exactness and degree-zero injectivity theorems of
`CorrectedGradedExactness`, and then uses
`isExactBeforeTerminal_of_jacquet` to reflect these conclusions to the
actual normalized complex. The degree support premise of that reflection
is supplied by `degreeObject_isInSupportCategory`.

`isExactBeforeTerminal_of_inputs` has the same conclusion for smooth `A`
in `Alg({I})`, using one supplied `CorrectedExactnessInputs` value.
It applies `isExactBeforeTerminal_of_correctedTargets` to that value's
eight fields.

The theorem assumes all eight structural inputs above; none is discharged
here. It needs no endpoint identities, no finite-length restriction, no
nonempty-root restriction and no rank-one or split-group hypothesis. Its
conclusion concerns only degrees strictly before `|S| - |I|`, and retains
the original terminal cokernel. This conditional result does not prove the
unconditional `RationalCorrectedTheorem36Statement`.
