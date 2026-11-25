# One-orbit source integral transport under normalized comparison

Waldspurger (2003), V.3.1 and VI.3.2, uses preservation of induced
coefficients under the extended normalized comparison. VII.2.4 uses
preservation of the induced tensor form, density and orbit measure as
well. The propositions here express the remaining identities for the
actual literal semistandard objects used by the source integrals.

- `CoefficientTransportStatement` compares the actual coefficient
  functions of the source and transported sections at every inducing
  representative. The preceding V.3.1 statement of the normalized Weyl/intertwiner
  coefficient comparisons uses the
  dynamic coefficient normalization. The literal comparison uses
  `SourcePacket.coefficientMap_leviNormalization` and
  `WeylSectionComparisonData.smoothComparison_apply`.
- `PairingTransportStatement` compares the source Schur degrees and the
  actual inverse-degree induced tensor forms. It uses
  `IntrinsicQuotientNormalization` on the compact Levi traces. The
  two quotient Haar comparisons and the existing
  `SourceDegree.FormalDegreeTransportStatement` specify the measure
  and degree interfaces for the dynamic-to-literal form comparison.
- `DensityTransportStatement` compares the two actual conditional
  continued inverse scalars on the unitary orbits. The displayed
  `OrbitPacketData` retain continuation, starting domains, generic
  irreducibility and full unitary inverse regularity. Their compacts
  agree with the compact of the normalized section comparison. The
  pure-conjugation scalar and density inputs are not proved
  here. The actual change of parabolic for the common Levi also
  enters this comparison.

The representative evaluation laws extend the stated coefficient and
pairing equalities to every orbit point. The two integral transport theorems
then use the proved measure-preserving orbit homeomorphism and equality
of the resulting integrands. The equalities use the same source
integrals as `GlobalSynthesis.componentPacket` and
`GlobalForm.componentForm`. They are conditional on the displayed
coefficient, scalar and pairing identities.
