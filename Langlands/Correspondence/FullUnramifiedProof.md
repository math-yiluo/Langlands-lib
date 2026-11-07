# Unramified normalization for every full correspondence

Worker 1273 supplies this proof, using Worker 1664's parameter-spectrum
construction and their final assembly check and instance-name correction.

`Langlands.Correspondence.fullCorrespondenceUnramified` proves the unchanged
[`FullCorrespondenceUnramifiedStatement.{uF, uP, uA} F`](FullSpecification.md).
For every prime `p`, every `F : PadicField.{uF} p`, every full map `c`, and every
geometrically normalized reciprocity candidate `e`, it derives
`UnramifiedCompatibility F e c` from exactly `IsFullCorrespondence F c` and
`IsGeometricReciprocity F e`. The field, parameter-carrier and
representation-carrier universes remain independent. All positive ranks,
arbitrary unramified quasi-character tuples and repeated eigenvalues are
included.

The proof is an internal deduction from the named Library results below.
It imports their proofs and introduces no additional mathematical premise.
The source meaning and normalization of the target remain those documented
in [`FullSpecification`](FullSpecification.md) and
[`UnramifiedNormalization`](UnramifiedNormalization.md). This Markdown
explains the implemented proof route.

First, unpack the full-correspondence predicate. Its rank-one compatibility
for the trivial quasi-character supplies a parameter `D0` and certifies that
`c 1 D0` is the trivial rank-one class. The composite of the trivial character
with the reciprocity candidate from that predicate is still trivial. Choose a
nontrivial unitary additive character using
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`, and obtain a self-dual
Haar measure from the full pair L-compatibility condition applied to `D0, D0`.

For any parameter `D` whose image has spherical spectrum `s`,
[`IsPairLCompatibleAt.standardEulerPolynomial`](StandardLPolynomial.md)
certifies its arithmetic polynomial `parameterEulerPolynomial F D` as the
supplied automorphic pair polynomial against `c 1 D0`. The proved theorem
[`sphericalStandardLComparison`](SphericalStandardLComparisonProof.md)
identifies that polynomial with `Eigenvalues.eulerPolynomial s`. This is the
local assertion `hpolynomial` in the Lean proof.

For each tuple `z` of nonzero complex numbers,
[`sphericalConstituentOfTuple`](../Representation/Unramified/SphericalConstituentChoice.md)
provides an actual irreducible admissible spherical constituent in the
independently prescribed representation universe. Rankwise surjectivity of
`c` gives a parameter preimage `E` of its class. The polynomial identity above
and
[`parameterEulerPolynomial_eq_eulerPolynomial_iff`](UnramifiedSpectrumClass.md)
identify `E` with `unramifiedSpectrumClass F (Eigenvalues.ofTuple z)`.
Consequently `c` sends this unramified class to the chosen constituent's class;
this is `hpreimage`.

The first component of `UnramifiedCompatibility` now follows in both
directions. Every unramified class is `unramifiedSpectrumClass F s` for some
unordered spectrum `s`; choose an enumeration and apply `hpreimage` to obtain
a spherical image. Conversely, a spherical representative has a spectrum by
[`sphericalSpectrumExistence`](../Representation/Unramified/SphericalSpectrumExistenceProof.md).
The identity `hpolynomial` and the arithmetic Euler converse show that its
parameter preimage is unramified, including zero monodromy.

For the second component, let `chi` be any tuple of unramified
quasi-characters and put `z = characterValues F chi`. Choose the same
unramified spectrum class and actual spherical constituent.
`isCharacterSumParameter_iff_eq_unramifiedSpectrumClass`, with the given
geometric normalization of `e`, identifies this parameter with the direct sum
of the Weil characters `chi i` composed with `e`, with zero monodromy.
The equality `hpreimage` gives its image under `c`. The constituent's
specification supplies the nonzero compact-fixed vector and a surjective
intertwiner from a subrepresentation of the normalized principal series of
`characterTuple F z`. Finally `characterTuple_characterValues` identifies
that series with the original `principalSeries F r chi`, producing precisely
the actual-object and subquotient witnesses required by the target.

The argument uses geometric reciprocity only through the proved character-sum
comparison, so it applies to every geometrically normalized candidate `e`
without identifying it with the candidate inside `IsFullCorrespondence`.
The theorem concludes both original compatibility conditions and leaves the
published statement and its imported definitions unchanged.
