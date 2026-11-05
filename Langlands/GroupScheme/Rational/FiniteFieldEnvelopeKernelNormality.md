# Finite-field normality from actual kernel and centralizer geometry

Worker 1556.

This internal assembly retains explicit geometric presentations and two global
proof inputs. It does not prove the unconditional
`FiniteFieldSolvableEnvelopeNormalityStatement`.

`EnvelopeKernelCentralizerGeometry D n q s` stores actual group schemes and maps
over the original field. Its first group maps as a closed subgroup to the
represented torus envelope `D.group` and compatibly into the ambient kernel
through `n`. The restriction of `q` to the envelope is the represented fppf
quotient by that subgroup. This kernel is smooth, connected, unipotent, and
split in the existing finite represented additive-series sense.

The second group is a closed subgroup of the ambient kernel and represents
`(torusCentralizer s).comap n` on every relative test scheme. It is smooth,
connected, and split unipotent. The existing scheme-theoretic intersection of
the two maps into the ambient kernel is also smooth, connected, and split.
The record includes no product-surjectivity or normality conclusion.

`TorusGeneratedEnvelope.isNormal_of_finiteField_kernelCentralizer` applies this
data to a sectioned torus quotient with smooth connected affine split unipotent
kernel over a finite field. The stable-vector statement and the exact
`RelativeRoot.FiniteFieldSplitUnipotentProductStatement` remain explicit
premises. The section factors through the envelope because it is a closed
ground-field torus. The existing rational torus-map correction then expresses
every rational ambient-kernel point as a product of a rational envelope-kernel
point and a rational centralizer point. The finite-field product statement
supplies smoothness and scheme-surjectivity of the original subgroup
multiplication morphism. Affineness of its source and target supplies
quasi-compactness, so the existing fpqc product normality theorem applies.
This step descends membership in the actual represented envelope along covers;
it retains normality on all relative tests, including nonreduced schemes.

`TorusGeneratedEnvelope.isNormal_of_finiteField_sectionedQuotient` specializes
this assembly to `SplitGeometricRadicalSectionedTorusQuotient G`. The stored
radical supplies smoothness, connectedness, unipotence, and closedness; its
affineness follows from its closed inclusion into the affine ambient group.
The conclusion concerns the unchanged `closedTorusEnvelope G`, using the
representation identity of `D`. The split geometric radical and quotient are
actual data; this theorem neither constructs the kernel/centralizer geometry
nor removes the two explicit global premises.

The provenance is direct composition of the imported Library interfaces in
`Rational.EnvelopeRationalProductFactorization`,
`Rational.EnvelopeProductNormality`,
`Rational.FiniteFieldSplitUnipotentProductStatement`, and
`Rational.PerfectFieldSectionedSolvableQuotient`. No additional external
mathematical assertion is introduced.
