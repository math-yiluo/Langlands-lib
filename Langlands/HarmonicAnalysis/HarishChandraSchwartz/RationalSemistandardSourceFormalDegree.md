# Actual source formal degree and intrinsic transport target

Worker 268, Task 7258. This derived unit supplies the actual Schur degree
on every intrinsic semistandard unitary discrete-series orbit and states
the exact remaining transport to its algebraic Levi model.

## Source and setup

Waldspurger (2003), registered `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
I.1, printed pp.240–241 (PDF pp.6–7), fixes the source measures. VI.1,
printed pp.295–296 (PDF pp.61–62), and VII.2, printed p.319 (PDF p.85),
use the source formal degree and its inverse in the induced tensor
pairing. The model-specific Lean adapters are internal consequences
and exact transport obligations for those constructions.

Declarations are in
`Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDegree`.
They use an arbitrary intrinsic semistandard triple, an actual
`LeviModel` over its literal all-test Levi and a `CompactData` picture.
The nonarchimedean local field and representation-carrier universes
are independent. Affineness, local finite type and the already published
semistandard structure retain the full nonsplit and positive
characteristic scope.

The literal central subgroup is `model.splitCenter a` for an actual
algebraic split component `a`. The literal quotient has its displayed
Borel measurable space and an inverse-invariant Haar measure `mu`.
The scheme-point central subgroup is `(rationalPoints.map a).range`.
Both actual images retain their normality instances. No arbitrary
central quotient, degree, comparison equivalence or measure is selected.

## Constructed degrees and proved laws

`intrinsicCompactOpenCofinal` proves compact-open cofinality on the
actual scheme-point group. It pulls an open subgroup to the literal
Levi through `model.pointHomeomorph.symm`, applies the existing
`compactOpenCofinal_levi`, and pulls the resulting compact open subgroup
back through `model.pointHomeomorph`. Compactness follows from the
homeomorphism's closed embedding, and inclusion from its inverse law.

`intrinsicInverseInvariant` proves inversion invariance of precisely
`SourceMeasure.intrinsicQuotientHaar model a mu`. The proof uses the
actual `SourceMeasure.centralQuotientHomeomorph`, composition of measure
pushforwards, and its compatibility with inversion. Haar and Borel
properties of that exact pullback are the existing source-measure
adapter's instances. There is no extra inverse-invariance premise on
the transported measure.

`orbitDegree` is the existing `discreteSeriesOrbitFormalDegree` on the
literal central quotient with the supplied Haar, using the actual
model norm-character family and the proved compact-open cofinality.
`orbitDegree_pos` specializes its existing positivity theorem.
`orbitDegree_eq_representationDegree` identifies this degree with
`representationFormalDegree` for every actual irreducible admissible
inducing representative of the same orbit, at the same quotient and
Haar. Its proof rewrites the orbit equality and applies the published
class-degree evaluation theorem. Thus representation and unitary-twist
choices in the literal source degree are already removed.

## Exact outstanding target

`FormalDegreeTransportStatement` is an **unproved Prop-valued target**.
For every literal `DiscreteSeriesClass omega`, it concludes equality of
its actual `discreteSeriesFormalDegree` with the degree of
`SourceMeasure.intrinsicDiscreteSeriesClass model a ha mu omega` on the
scheme-point quotient. The latter uses the prescribed
`SourceMeasure.intrinsicQuotientHaar` and the compact-open cofinality
proved here. The group identification, central quotient map, Haar
pullback and inducing class are all fixed existing constructions.
The target does not take its degree equality as data.

This target isolates the remaining Schur-normalization transport through
the actual model inclusion. It introduces no new scalar positivity,
continuation, Plancherel density or standard VI.3.1 estimate obligation.
Its proof belongs to a successor after publication, while the original
Schur/class-degree theorems and the source-measure transport remain the
precise preceding interfaces. The exact standard source-form/core
specialization is separately proved in
`RationalSemistandardStandardFormComparison`; this general target does
not claim that arbitrary model transport has thereby been proved.
