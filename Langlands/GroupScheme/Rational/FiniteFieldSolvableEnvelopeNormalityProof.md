# Torus-envelope normality for solvable groups over finite fields

Authors: Worker 1556 and Worker 1619.

`Langlands.GroupScheme.finiteFieldSolvableEnvelopeNormality` proves exactly
`Langlands.GroupScheme.FiniteFieldSolvableEnvelopeNormalityStatement.{u}`.
For every finite field `k : Type u` and every smooth connected affine group
scheme `G` over `Spec k` satisfying `IsSolvableGroupScheme G`, the fixed
`closedTorusEnvelope G` is normal. The universe `u` is arbitrary.

The conclusion uses the original `SubgroupFunctor.IsNormal`: conjugation by
every point of `G` preserves the envelope on every relative test scheme,
including nonreduced tests. The theorem has no additional premises.

## Implemented proof

Choose `D := smoothTorusGeneratedEnvelope G` from
[`SmoothTorusGeneratedEnvelope`](SmoothTorusGeneratedEnvelope.md).
This is an actual closed subgroup representing the unchanged envelope on
every test scheme. The accompanying theorems
`smoothTorusGeneratedEnvelope_smooth` and
`smoothTorusGeneratedEnvelope_connectedSpace` give its smoothness and
connectedness.

A finite field is perfect. The construction
`perfectFieldSectionedSolvableTorusQuotient` in
[`PerfectFieldSectionedSolvableQuotient`](PerfectFieldSectionedSolvableQuotient.md)
therefore gives an actual split geometric unipotent radical of `G` and a
sectioned fppf torus quotient of that same radical inclusion. Radical existence,
Galois descent, and perfect-field splitness are proved inputs of this
construction. Its two remaining statement inputs are supplied by the exact
published theorems `solvableTorusQuotient` in
[`Absolute.SolvableTorusQuotientProof`](../Absolute/SolvableTorusQuotientProof.md)
and `RelativeRoot.splitUnipotentStableVectorSubgroup` in
[`SplitUnipotentStableVectorProof`](SplitUnipotentStableVectorProof.md).
The algebraically closed quotient theorem is used through the construction;
no algebraic closedness or splitness assumption is imposed on `k` or `G`.

For this quotient data `a`,
`D.sectionedQuotientKernelCentralizerGeometry a` from
[`EnvelopeKernelCentralizerAssembly`](EnvelopeKernelCentralizerAssembly.md)
constructs the actual kernel of the quotient restricted to the envelope,
the centralizer of its torus section inside the original radical, and their
scheme-theoretic intersection. The record supplies their smoothness,
connectedness, and split unipotence, together with the all-test subgroup
identities and the restricted fppf quotient. The torus section factors through
`D` because it is a closed ground-field torus.

Finally, apply
`D.isNormal_of_finiteField_sectionedQuotient` from
[`FiniteFieldEnvelopeKernelNormality`](FiniteFieldEnvelopeKernelNormality.md).
Its global inputs are supplied by the same stable-vector theorem and
`RelativeRoot.finiteFieldSplitUnipotentProduct` in
[`FiniteFieldSplitUnipotentProductProof`](FiniteFieldSplitUnipotentProductProof.md).
The criterion first obtains a factorization of every rational radical point
by an envelope-kernel point and a centralizer point. The product theorem uses
split-unipotent point counts and geometric orbit arguments to prove smoothness
and scheme-surjectivity of the actual multiplication morphism. Affineness
also gives quasi-compactness. The criterion then descends membership in the
represented envelope along fpqc covers and returns normality of the original
`closedTorusEnvelope G` on every relative test scheme.

## Provenance

This proof is an internal composition of the imported Library constructions
and exact theorems named above. The source and intended meaning of the target
are recorded in
[`FiniteFieldSolvableEnvelopeNormalityStatement`](FiniteFieldSolvableEnvelopeNormalityStatement.md).
The implementation follows the finite-field product and fpqc descent route.
All structural statements required by the assembly are discharged by imported
proofs.
