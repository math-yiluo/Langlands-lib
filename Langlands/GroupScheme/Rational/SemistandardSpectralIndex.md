# Intrinsic semistandard spectral indices

Worker 568, Task 7229. Source: Waldspurger (2003), I.1, printed pp.238–239,
and VI.3, printed p.305, registered source `waldspurger-2003-plancherel`, DOI
10.1017/S1474748003000082. These original pages were read directly. This is a
construction with proved elementary laws and explicit unproved geometric targets.

## Carrier and source comparison

`Langlands.GroupScheme.SemistandardParabolicFunctor i` is the source's set of
actual parabolic subgroup functors containing the fixed torus: `range i ≤ P`
on every test scheme. `SemistandardSpectralIndex i` records the three actual
subgroup functors P, M and U, with `range i ≤ M` and the published predicate
`IsParabolicWithLeviAndRadical P M U`. This predicate requires actual represented
parabolic, connected reductive Levi and geometric unipotent radical models and
the Levi decomposition on every test scheme. The models occur only existentially
in a proposition. The carrier contains no chosen scheme, cocharacter, chamber,
root presentation or proof witness as index data.

`SemistandardSpectralIndex.ext` proves equality from equality of all three
subgroup functors. Functor equality means equality on every test scheme, using
`SubgroupFunctor.ext`. `levi_le_parabolic` and `radical_le_parabolic` extract
the all-test inclusions. `toParabolic` forgets M and U.

The exact Prop-valued targets `SemistandardSpectralCoverageStatement` and
`SemistandardSpectralUniquenessStatement` assert surjectivity and injectivity of
`toParabolic`, respectively, under connected reductivity and maximality of the
fixed split torus. Together they identify the constructed triple carrier with
the source's parabolics. These are unproved here. In particular, the construction
does not claim uniqueness of M or U merely from the existence of a decomposition.

`SemistandardSpectralLevi i` is the image of the Levi projection, as an actual
subgroup functor with an existential Prop witness. `SemistandardSpectralParabolicFiber i M`
is the fiber over that exact subgroup functor: the unquotiented P(M) needed by
the synthesis coefficient on p.305. `toLevi` and `inFiber` give its projections.
`nonempty_semistandardSpectralParabolicFiber` proves nonemptiness by unpacking the
image witness; it requires no finiteness assumption. Once the source uniqueness
target is proved these fibers count parabolics, without duplicating Levi/radical
choices.

## Dynamic and existing standard triples

`SemistandardSpectralIndex.ofCocharacter hG ζ` uses the actual dynamic
P(ζ), Z(ζ), U(ζ) in the fixed torus. Its structural property is proved by
`Dynamic.isParabolicWithLeviAndRadical_of_structural` applied to the published
proofs `parabolicDynamic`, `dynamicCentralizerReductive` and
`dynamicGeometricUnipotentRadical`. The containment of the torus in Z(ζ) uses
the commuting torus. No unproved structural statement is supplied as a hypothesis
of this constructor.

`ofCocharacter_eq` is equality whenever the actual triples agree.
`ofCocharacter_zsmul` proves that every positive integral multiple has the same
index, including multiples divisible by the residue characteristic. The proof
uses the published all-test `relativeRootSignsDetermineDynamic` and preservation
of nonnegative, zero and positive integer pairings under positive scaling.

`ofStandard hG hi ν hν J hJ` reuses exactly the existing choice-free standard
parabolic, Levi and radical functors. Here ν is generic and J is any subset of
its simple relative roots. It uses the proved `standardCocharacter` only to
establish the structural property of those existing functors. Its three
projection formulas are definitional. `ofStandard_eq_ofCocharacter` identifies
it with every standard cocharacter for the same J, simultaneously on all tests.
This also specializes to the existing finite-simple-root indexing by taking
`J = RationalPointFamily.rootSet i ν I`.

## Targets and scope

All five statement declarations are proposition definitions, not theorems:

- `SemistandardSpectralCoverageStatement`: actual source parabolics are covered.
- `SemistandardSpectralUniquenessStatement`: the distinguished Levi and radical
  are uniquely determined by P when M contains the fixed maximal split torus.
- `SemistandardSpectralDynamicCoverageStatement`: every indexed triple comes
  from a cocharacter in this same fixed split torus.
- `SemistandardSpectralFinitenessStatement`: the whole semistandard index is finite.
- `SemistandardSpectralFiberFinitenessStatement`: each P(M) is finite and nonempty.

These targets quantify over every field k, connected reductive G and actual
maximal split torus i; they have no desired coverage, uniqueness or finiteness
conclusion among their premises. The nonempty component of the fiber target is
already proved independently; `semistandardSpectralFiberFiniteness_of_finiteness`
proves the remaining implication from whole-index finiteness by subtype
finiteness. The geometric finiteness targets are unrelated to the representation
theoretic orbit-finiteness theorem VIII.1.2.

The construction permits nonsplit groups and arbitrary characteristic and makes
no assertion about Fourier families, Weyl or intertwiner invariance, synthesis,
measures, or Plancherel. All original-source geometry not supplied by the imported
constructors remains explicitly visible in the targets above.
