# Regularity of the actual semistandard Fourier components

The module `RationalSemistandardFourierRegularityProof` proves the four
regularity propositions stated in `RationalSemistandardFourierFamily`. All
names are in the namespace `Langlands.HarishChandraSchwartz`.

| Theorem | Proposition proved |
| --- | --- |
| `rationalSemistandardFourierContinuity` | `RationalSemistandardFourierContinuityStatement` |
| `rationalSemistandardFourierSmoothness` | `RationalSemistandardFourierSmoothnessStatement` |
| `rationalSemistandardFourierCompactLevel` | `RationalSemistandardFourierCompactLevelStatement` |
| `rationalSemistandardFourierFamilySmoothness` | `RationalSemistandardFourierFamilySmoothnessStatement` |

The module repeats the variable blocks of `RationalSemistandardFourierFamily`
in the same order and with the same names, so each theorem's type is its
proposition applied to the proposition's own binders: an arbitrary
nonarchimedean local field in universe `u`, inducing representations with
carriers in the independent universe `uV`, and the ambient connected
reductive group with its maximal split torus, generic cocharacter, compact
Iwasawa subgroup `K`, matrix representation and square-integrable weight.
The three component theorems further take the literal semistandard
parabolic `p` with its Levi model `m`, compact data `d`, modular
normalization, inducing representation, central subgroup, quotient Haar
measure and tempered-coefficient hypotheses. The product theorem takes the
split components `a` with their quotient measures, compact data, modular
normalizations and tempered hypotheses at every index. The only premise
used beyond these binders is the proposition's own
`RationalSemistandardFourierAnalyticInputs` hypothesis on the Levi measure
`muL`, the radical measure `muU` and the Levi weights `XiM`, `sigmaM`. The
module declares the same two local instances as the statement module (a
compact open subgroup of the rational points, from
`Langlands.BruhatTits.rationalPointCompactOpenSubgroup`, and local
compactness of each closed parabolic), so the Schwartz space and the VI.3
section space are the ones of the statements.

## Continuity

`rationalSemistandardFourierContinuity` first turns the instance-valued
fields of the analytic inputs into local instances: inversion invariance
and sigma-finiteness of the ambient Haar measure, left, right and inversion
invariance and s-finiteness of `muL`, and left and right invariance and
s-finiteness of `muU`. Applying `compactOpenCofinal p d` to the whole Levi
gives a compact open subgroup of the Levi, hence a nonempty type of compact
open subgroups, which `fourierOrbitLaurentSectionCLM` uses for its base
compact open subgroup. The field `laurent_height` gives a constant `B` with
`‖laurentExponent … x‖ ≤ B * (1 + sigmaM x)` for the Laurent exponent of the
model's unitary coordinates.

The continuous linear map is `fourierOrbitLaurentSectionCLM` of the module
`FourierOrbitContinuity`, applied to the following data:

- the semistandard decomposition `decomposition p`, the closedness results
  `isClosed_radical p` and `isClosed_parabolic p`, and from the compact data
  the projection continuity, the compact open subgroup `d.compact`, its
  compactness and the factorization membership;
- reductive unimodularity of the rational points
  (`RationalPointFamily.rationalReductiveUnimodularity`) and the modular
  normalization;
- the norm characters of the Levi model, its unitary coordinates
  `m.unitaryCoordinates.toMulEquiv`, their continuity and their Laurent
  property `m.unitaryCoordinates_hasLaurent`;
- Levi compact-open cofinality `compactOpenCofinal p d`, the central
  subgroup and quotient measure, and the transport of square integrability
  along the unitary orbit, `unitaryOrbitRepresentative_isDiscreteSeries`;
- the ambient weights `rationalL2Weights`, `rationalXi_inv`,
  `rationalHeight_inv` and `rationalTranslationWeights`, and the tempered
  hypotheses of the induced representatives;
- the remaining fields of the analytic inputs: compact volumes, radical
  unimodularity, the Levi `L2Weights`, temperedness of the base and of
  every orbit representative, the inversion identities of `XiM` and
  `sigmaM`, the constant-term data, conjugation modulus and estimate, the
  Levi translation weights, the compact factorization criterion and the
  double integrability, together with the Laurent bound above.

The domain of this map is the published rational Schwartz space and its
codomain is `rationalSemistandardFourierOrbitSpace p m d pi`, the published
`OrbitSectionSpace` with its VI.3 topology. The required identity of raw
sections holds by `rfl`. The underlying section of
`fourierOrbitLaurentSectionCLM` is `fourierOrbitSection` by definition, and
`rationalSemistandardFourierOrbit` is that `fourierOrbitSection` at the
literal semistandard data, as the reflexive lemma
`rationalSemistandardFourierOrbit_eq` records.

## Component smoothness

`rationalSemistandardFourierSmoothness` takes the map `L` from the
continuity theorem and rewrites the raw section of `f` as the underlying
value of `OrbitSectionSpace.toSections (L f)`. That value lies in the
published smooth orbit sections for the same norm characters, coordinates,
decomposition and compact data, which is `smoothOrbitSections m d pi` by
definition. The membership is the subtype property of `toSections (L f)`.

## Fixed level and common compact range

`rationalSemistandardFourierCompactLevel` fixes an open subgroup `H` of the
rational points with `H ≤ d.compact`. The submodule `W` is
`orbitSectionFixedCoefficients (decomposition p) d.compact pi H` of the
module `OrbitSectionFixedTensor`: the vectors of the compact picture fixed
by `(H ⊓ d.compact) × (H ⊓ d.compact)`. It depends only on `H`, not on the
Schwartz function or on the torus parameter. It is finite dimensional by
`finiteDimensional_orbitSectionFixedCoefficients`, from compactness of
`d.compact` and compact-open cofinality of the Levi.

Let `f` be `H`-bi-invariant. For `(x₁, x₂)` in `H × H`, the translate of `f`
by `(x₁, x₂)` is `f` itself, by `IsBiInvariant.translate_eq` and
extensionality in the Schwartz space. The published translation identity
`rationalSemistandardFourierOrbit_translate` (Waldspurger VII.1.1(i)) says
that the section of the translate is the section of `f` acted on by
`productInducedOrbitRepresentation` at `(x₁, x₂)`. Hence the section of `f`
is fixed by `H × H`. With component smoothness this is membership in
`orbitSectionLevelSubmodule … H`, which is the intersection of the smooth
sections with the `H × H` invariants. For every open `H' ≤ H`, membership in
the level of `H'` follows by `orbitSectionLevelSubmodule_antitone`.

For the compact range, `orbitSectionLevelFixedRestriction` sends a section
of level `H` to its compact restriction, with values in `W`. At the section
of `f` and a torus parameter `z`, its value is by definition the compact
restriction `productInducedFamilyRestriction` of the pulled-back section in
the statement, which therefore lies in `W`.

## Smoothness of the full product

`rationalSemistandardFourierFamilySmoothness` fixes an index
`t = (p, O)` of the full dependent product. The component of
`rationalSemistandardFourierFamily` at `t` is, by definition, the raw orbit
section at `p` for the chosen Levi model `chosenLeviModel p`, the compact
data `d p`, the modular normalization at `p`, the orbit representative
`orbitRepresentative … t.2`, the split center `splitCenter (a p)` with its
centrality, and the measure `muM p`. Its square integrability is
`orbitRepresentative_isSquareIntegrable`, and the tempered hypothesis at
each unitary twist is the family's hypothesis applied to the twist, whose
square integrability is again `unitaryOrbitRepresentative_isDiscreteSeries`.
The target `rationalSemistandardThetaComponentSpace a ha muM d t` is
`smoothOrbitSections` at the same model, compact data and representative,
so component smoothness at these data, under the analytic inputs supplied
at `t`, proves the statement.

## Source

The propositions formalize the regularity part of
[Waldspurger (2003), Proposition VII.1.3, printed p. 316 (PDF p. 82)](https://doi.org/10.1017/S1474748003000082),
the registered source `waldspurger-2003-plancherel` with SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The Lean proofs do not follow Waldspurger's argument. They reduce the
literal semistandard data to the generic Laurent-coordinate continuity
theorem `fourierOrbitLaurentSectionCLM`, the translation identity of the
Fourier orbit and the fixed-coefficient finiteness of
`OrbitSectionFixedTensor`.
