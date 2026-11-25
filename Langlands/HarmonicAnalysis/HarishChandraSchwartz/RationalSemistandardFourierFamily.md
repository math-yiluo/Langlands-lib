# The actual full semistandard Fourier product

This module, the second step of the full Fourier product construction after
`RationalSemistandardFourierTransform`, constructs the raw family `psi_f` in the
full intrinsic dependent product of `RationalSemistandardSpectralFamily`. It supplies elementary coherence,
base-point and model transport, and actual `G × G` equivariance. The substantive
regularity and cross-normalization comparisons are named, unproved Prop targets.

## Original source and mathematical scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), registered as
`waldspurger-2003-plancherel`: VII.1, printed pp. 313–317, especially the
definition of `psi_f[O,P]` and Proposition VII.1.3 on printed p. 316
(PDF p. 82); VI.3 defines the full index and its section spaces, with `Theta`
and the direct sum on printed p. 305 (PDF p. 71).

The full Fourier family here takes values in a **product**, as required before
VIII.1 finiteness. The source's finite-support direct sum is an input space for
wave packets; it is not the codomain of the general Fourier family in this module.
The uniform finite-dimensional compact range in the compact-level target is an
internal formulation of the finite compact-picture condition used by the
published standard smoothness and continuity interfaces. It does not assert
finiteness of the set of nonzero `(P,O)` components.

The scope and scalar conventions are those of
`RationalSemistandardFourierTransform`: independent field and representation
universes, arbitrary nonarchimedean local field, affine locally finite type
connected reductive ambient group, canonical rational-point topology, and
complex `SmoothRep`. The intrinsic semistandard index includes all actual
semistandard parabolic/Levi/radical triples. There is no splitness,
quasisplitness, characteristic-zero, positive-rank, or induced-irreducibility
assumption.

## Raw construction before analytic lifting

`rationalSemistandardFourierOrbit` is a complex-linear map into the exact
`RationalSemistandard.OrbitSections m pi` of the dependency. At every actual
irreducible admissible inducing representative `A` in the unitary orbit it
returns `rationalSemistandardInducedFourierTransform ... A.val.obj ... f`.
The square-integrability proof is transported within the orbit using
`unitaryOrbitRepresentative_isDiscreteSeries`. The quotient Haar measure and
formal degree are the supplied actual ones throughout.

`rationalSemistandardFourierFamily` specializes this construction to
`chosenLeviModel p`, the actual split image `(chosenLeviModel p).splitCenter (a p)`,
and the chosen actual discrete-series representative at each intrinsic full
index `t = (p,O)`. Its codomain is exactly
`RationalSemistandardThetaSections a ha muM`. Neither definition consumes a
smoothness witness or a support hypothesis. Both are already linear maps.
The two `..._apply` lemmas give reflexive evaluation formulas down to the actual
Fourier tensor, for downstream fixed-vector and support arguments.

The preceding inputs are visible: compact data `d p`, modular comparison
`hdelta p`, ambient `SquareIntegrableWeight`, and tempered coefficient growth of
actual normalized inductions. For the full family the last input is quantified
over every actual discrete series modulo the indicated split center. Quotient
measures are Borel Haar measures invariant under inversion. Ambient left and
right invariance are retained; coherence additionally uses ambient inversion
invariance. These analytic inputs remain obligations for other modules,
not permanent external structural assertions.

## Elementary laws and declaration dependencies

All names below are in `Langlands.HarishChandraSchwartz` unless a different
namespace is written explicitly.

| Declaration | Implemented result and immediate dependency |
| --- | --- |
| `rationalSemistandardFourierOrbit`, `..._apply`, `..._eq` | Actual tensor at every inducing representative; equality with the published generic `fourierOrbitSection` is reflexive. |
| `rationalSemistandardFourierOrbit_coherent` | Every inducing equivalence, including every self-twist, by the actual transport theorem of `RationalSemistandardFourierTransform`. |
| `rationalSemistandardFourierOrbit_baseChange` | The published `productInducedOrbitBaseEquiv` keeps the same actual object and tensor at each point; reflexivity and proof irrelevance. |
| `rationalSemistandardFourierOrbit_modelChange` | The specified `LeviModel.orbitSectionsModelEquiv` fixes literal Levi elements and representation values; reflexivity and proof irrelevance. |
| `rationalSemistandardFourierOrbit_translate` | Pointwise application of VII.1.1(i) from `RationalSemistandardFourierTransform`. |
| `rationalSemistandardFourierFamily`, `..._apply` | Full dependent product and its exact tensor evaluation; pointwise linearity and reflexivity. |
| `rationalSemistandardFourierFamily_baseChange` | The dependency's actual `orbitSectionsBaseEquiv` sends the full component to its raw construction at any other representative of the same actual orbit; reflexivity. |
| `rationalSemistandardFourierProductRepresentation` | Pointwise action of `productInducedOrbitRepresentation`, hence of the actual normalized induced coefficient fibers. The representation laws follow from their pointwise laws. |
| `rationalSemistandardFourierFamily_translate` | Full product VII.1.1(i), by the orbit translation theorem at every index. |
| `rationalSemistandardFourierFamily_coherent` | Coherence at every full component, by the orbit coherence theorem. |
| `rationalSemistandardFourierOrbitSpace_standard` | The standard component space is the existing `rationalInducedOrbitSectionSpace`; reflexivity. |

The translation is `f(x) ↦ f(g2⁻¹*x*g1)` with the action at `(g1,g2)`, exactly as
in `RationalSemistandardFourierTransform`. No transport map is chosen to force these identities.

Changing an auxiliary Levi model reindexes actual unitary characters and
representatives by the dependency's specified model comparison. The transform
itself uses only the literal Levi. For changes of the split presentation or
quotient measure, `rationalSemistandardFourier_normalization` of `RationalSemistandardFourierTransform`
requires equality of the actual formal degrees; arbitrary Haar rescaling does
not disappear. Smooth comparison between different model coordinates and
compact choices remains the dependency's `ModelSmoothComparisonStatement`.

## Exact regularity targets

`RationalSemistandardFourierAnalyticInputs` is a Prop structure of preceding
inputs to the published `fourierOrbitSection_mem_smooth_of_hasLaurent` and
`fourierOrbitLaurentSectionCLM`. It contains no membership or continuity claim
about the new Fourier section. Its fields retain:

- Ambient inversion invariance, sigma-finiteness, and volume one for the
  actual compact picture; radical unimodularity.
- A Levi measure with left/right/inversion invariance and s-finiteness,
  `L2Weights` for the supplied Levi functions `XiM` and `sigmaM`, tempered
  coefficients for the base and every orbit representative, and their
  inversion identities and translation weights.
- A radical measure with left/right invariance and s-finiteness, the actual
  `ConstantTermData` and `IsConjModulus` for the radical Haar modulus, and
  `ConstantTermEstimate` between the ambient rational weights and the Levi
  weights.
- The exact compact Levi/radical factorization criterion and volume-one
  conditions for both intersections.
- A height bound for the actual Laurent exponent of the dependency's canonical
  finite circle coordinates, and the double-integrability condition for the
  actual coefficient integrand against every Schwartz function.

The Levi weight functions are supplied preceding data satisfying these precise
conditions. Existence and comparison with weights on a representing rational
Levi scheme are not silently asserted. In the existing standard specialization
these are `rationalLeviXi` and restricted `rationalHeight`. The standard
interfaces `rationalFourierOrbitSmoothSectionLinear` and
`rationalFourierOrbitSectionCLM` retain their closed matrix representation,
height compatibility, Levi Iwasawa pair and `IsRationalLeviTempered` hypotheses,
Levi square-integrable weights, actual measure normalizations, constant-term
estimate, valuation-height bound and double-integrability input. Their generic
input collection is preserved here; these obligations are not discharged by
importing those standard interfaces.

The following are **unproved named targets**, each a Prop-valued definition:

| Target | Conclusion after the preceding analytic inputs |
| --- | --- |
| `RationalSemistandardFourierSmoothnessStatement` | The raw orbit section belongs to the dependency's coherent `smoothOrbitSections m d pi`. |
| `RationalSemistandardFourierFamilySmoothnessStatement` | At every full index, the actual family component belongs to `rationalSemistandardThetaComponentSpace a ha muM d t`. |
| `RationalSemistandardFourierCompactLevelStatement` | For every open `H ≤ d.compact`, one finite-dimensional submodule of the actual compact picture contains all torus values for every `H`-bi-invariant input `f`; the raw section belongs to the exact `orbitSectionLevelSubmodule ... H` and to every smaller open level. |
| `RationalSemistandardFourierContinuityStatement` | There exists a continuous complex-linear component map in the existing Schwartz and VI.3 inductive-limit section topologies whose raw section is the already defined Fourier section. |

The compact-level target's submodule is uniform in both `f` at that fixed level
and its unitary torus parameter. Refinement means the inclusion for every
`H' ≤ H`; it does not change the Fourier index set. The existing generic
`orbitSectionLevelSubmodule_antitone` describes those level inclusions.

`rationalSemistandardFourierOrbitSpace` is the actual `OrbitSectionSpace`,
with its existing topology; it is not supplied an arbitrary topology.
`rationalSemistandardFourierOrbitSmooth` explicitly consumes preceding smooth
membership and returns a typed linear component map. Likewise
`rationalSemistandardFourierSmoothFamily` consumes membership at every component
and lands in a product of smooth component submodules. This carrier has no
support condition. Neither conditional lift is a proof of its premise.

## Standard restriction and normalization

`RationalSemistandardStandardFourierNormalization` records the exact compact
and degree conditions needed to compare with independently supplied standard
split/measure data: the standard slice uses `standardCompactData`, and the
actual formal degrees agree on every common discrete-series inducing object.
It asserts no Fourier equality. It is an explicit normalization condition,
not a theorem that all independently scaled Haar data satisfy it.

`RationalSemistandardFourierStandardComparisonStatement` is the named unproved
cross-normalization target. Given that normalization and the dependency's
`RationalSemistandardStandardDiscreteSeriesComparison`, it concludes equality
of the full family after **the specified** `rationalStandardFullRestrict` with
`rationalFourierThetaFamily`. The restriction already includes actual orbit
reindexing, representative base change, and scheme-model comparison; no free
comparison equivalence is a parameter. The existing standard transform's closed
matrix, height, Levi Iwasawa and temperedness inputs remain explicit. The existing
`rationalOrbitSectionsBaseEquiv_rationalFourierThetaFamily` and the proved
`rationalSemistandardFourierFamily_baseChange` supply the two representative
comparisons independently of that full comparison target.

## Dependencies and related results

The construction imports the exact carriers of `RationalSemistandardSpectralFamily`
and the actual operator of `RationalSemistandardFourierTransform`. It does not
reconstruct an invariant projector, synthesis, density or global form. V.3
normalized comparison and VII.1.4 covariance are a separate step, using the
specified normalized Weyl/intertwiner comparison of V.3 and the invariant
predicate of the invariant spectral families. General Fourier support
finiteness, VII.2.5 and VIII.1 inversion are not treated here.
