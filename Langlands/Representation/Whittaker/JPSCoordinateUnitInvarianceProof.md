# Uniform coordinate-unit invariance for actual JPS coordinate germs

`Langlands.Whittaker.jpsCoordinateUnitInvariance.{uF}` proves the complete
closed proposition
`Langlands.Whittaker.JPSCoordinateUnitInvarianceStatement.{uF}`. Its field
universe is unrestricted. The proof imports the published statement and
uses the actual objects from `JPSFunctionSpace` throughout.

The theorem quantifies every prime, every p-adic field `F`, every supplied
`T : F.TopologicalData`, every rank `n`, actual function space `W`, and
coordinate `i : Fin n`. Its hypotheses are exactly
`IsLocallyConstantSpace W T` and `HasFiniteCoordinateOperatorSpan W T i`.
The latter is finite dimensionality of the complex span of the actual
operators `sigma W T i u`. Neither `W` nor `CoordinateGerm W T i` is
assumed finite dimensional. No representation smoothness, admissibility,
finite generation, support condition, or invariance certificate is assumed.
At rank zero the coordinate quantification is vacuous.

All topology instances refer to the supplied `T.topology`: the field
topology, the induced units topology, the product topology on
`Torus F n = Fin n → F.Carrierˣ`, and subgroup subtype topologies.
`T.valuativeRel`, `T.localField`, and `T.fieldT2` install the corresponding
valuative, local-field, and Hausdorff certificates. The normalized absolute
value is the one belonging to `T`, normalized by its residue cardinality.

## Norm-one units and decreasing regions

`normOneUnits T` is the kernel of the multiplicative normalized absolute
value on `F.Carrierˣ`; its elements have absolute value one. Compactness is
the imported theorem
`Langlands.PadicField.TopologicalData.isCompact_normalizedAbs_eq_one_units`.
To prove openness, the implementation identifies this subgroup with the
preimage of the valuation-one sphere under `Units.val`. That sphere is
open by `Valuation.isOpen_sphere`, the normalized absolute value and
valuation have the same one-fiber, and the unit-value map is continuous.

The thresholds `coordinateThreshold m = 1 / (m + 1)` are positive,
antitone, and cofinal at zero: every positive real number exceeds one of
them. Each associated region includes every entire torus tuple satisfying
the bound on coordinate `i`, with no bounds on the other coordinates.

## Finite detection using actual representatives

Write `Q = CoordinateGerm W T i` and
`S = Submodule.span ℂ (Set.range (sigma W T i))`. The finite-span
hypothesis makes `S` finite dimensional. The imported theorem
`Langlands.exists_finset_eq_zero_of_apply_eq_zero` chooses a finite set
`t` of actual germs such that an operator in `S` vanishing on every member
of `t` is zero. This theorem is in
`Langlands.Representation.Smooth.FiniteOperatorExpansionProof`; the
detector itself requires no smoothness assumption on the acted-on space.

The actual quotient projection `germMap` is surjective. The algebraic
vector-space splitting theorem
`LinearMap.exists_rightInverse_of_surjective` supplies a complex linear
section `L : Q →ₗ[ℂ] W.toSubmodule`. This is an algebraic choice of actual
representatives; it asserts no continuity of the section.

For `A : S`, `detectorLift` is the scalar function on `t × Torus F n`
whose value at `(q,a)` is `(L (A q)).val a`. This is linear in `A`.
Its range `V` is finite dimensional. Moreover, restriction of `V` to
every threshold region is injective. Indeed, agreement of the two lifted
functions throughout that region says that `L ((A - B) q)` vanishes
there for every detector `q`. The actual kernel law
`germMap_eq_zero_iff` and the section identity give `(A - B) q = 0`.
Finite detection then gives `A = B`. This also proves injectivity of
`detectorLift` on the whole domain.

For a norm-one unit `u`, let `v u` be the element of `V` obtained by
lifting the actual operator `sigma W T i u`. The corresponding scalar
family is

```text
fdet u (q,a) = (L q).val (a * coordinateEmbedding i u).
```

For each `(q,a)` this is locally constant in `u`: `L q` belongs to `W`,
its scalar function is locally constant by hypothesis, and multiplication
and the coordinate embedding are continuous in the supplied topology.

For each fixed `u`, this family eventually agrees with `v u` on a single
threshold region. The actual intertwining identity `sigma_apply_mk`
shows that
`coordinateRepresentation W i u (L q) - L (sigma W T i u q)` has zero
germ. The kernel law gives a positive threshold for every `q`. There are
only finitely many detectors, so a finite maximum of threshold indices
works for all of them at once and for every entire torus tuple.

## A common compact open kernel

Apply the published theorem
`Langlands.Topology.baireFiniteDimensionalGermConstancy.{uF,uF}` to
`X = t × Torus F n`, `Y = normOneUnits T`, the decreasing threshold
regions, `V`, `fdet`, and `v`. The actual compact Hausdorff group `Y`
is nonempty and Baire. The preceding construction supplies injective
restriction, locally constant scalar evaluations, and eventual agreement.
This gives a nonempty open subset of `Y` on which `v` is constant.
Injectivity of `detectorLift` makes the actual operators `sigma` equal
throughout that subset.

Let `K = normOneUnits T` and restrict `sigma` to `K`. Its algebraic kernel
`H` contains an identity neighborhood: choose `u₀` in the open constancy
set and pull that set back by `u ↦ u₀ * u`. On this neighborhood,
`sigma (u₀ * u) = sigma u₀`, so the homomorphism law gives `sigma u = 1`.
A subgroup containing an identity neighborhood is open. An open subgroup
is also closed, hence `H` is compact in compact `K`.

The image `U` of `H` under the subgroup inclusion into `F.Carrierˣ` is
open because `K` is open and the subtype inclusion is an open map.
It is compact as the continuous image of compact `H`. It lies in `K`,
and therefore has absolute value one. Its defining kernel condition
shows that every member acts trivially on every element of the actual
quotient `Q`. The construction chooses `U` before any representative.
No topology on `Q` or continuity of its operator action is assumed.

## A threshold uniform in all units and all other coordinates

Fix an actual representative `f : W.toSubmodule`. For each `m`, define
`coordinateThresholdStabilizer` inside `U` to consist of the units fixing
`f` at every torus tuple in the `m`th region. It is a subgroup: multiplication
and inversion preserve this same region because the units have normalized
absolute value one. Local constancy of `f` gives continuity of every
scalar translate as a function of `u`; the stabilizer is an arbitrary
intersection of closed scalar equalizers and is therefore closed in `U`.
These subgroups increase as the threshold decreases.

They cover `U` pointwise. For each `u : U`, the kernel property makes
`coordinateRepresentation W i u f - f` have zero actual germ.
`germMap_eq_zero_iff` gives a positive threshold uniform in the entire
torus tuple. Cofinality supplies an index `m` for this unit.

The published theorem
`Langlands.Topology.compactGroupClosedSubgroupCover.{uF}`, applied to the
actual compact Hausdorff group `U`, now gives one index `m` at which this
closed increasing stabilizer equals the whole group. Thus
`ε = coordinateThreshold m` is positive and works simultaneously for all
torus tuples satisfying the coordinate bound and every `u ∈ U`.
The quantifier order is exactly
`∃ U, … ∧ ∀ f, ∃ ε > 0, ∀ a, … → ∀ u ∈ U, …`.

The finite detector may be empty and the finite-dimensional range may
have dimension zero. The argument uses neither a positive-dimensional
basis nor a nonempty detector family. The finite maximum, algebraic
section, generic Baire theorem, and subgroup-cover theorem all retain
these cases.

## Dependencies and provenance

The substantial generic prerequisites are imported by their published
Lean names: the finite-operator detector, finite-dimensional Baire germ
constancy, compact-group closed-subgroup cover, and norm-one compactness.
The remaining adapters above are proved directly for the actual JPS
quotient and coordinate action. The statement pair and its imports are
unchanged. The proof is in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

Worker 454 implemented the actual-quotient application. Worker 625
supplied its unformalized finite-detection/Baire/kernel and stabilizer-cover
route. Worker 345 implemented the generic Baire proof, Worker 451 its
statement, and Worker 101 the generic subgroup-cover proof. Those
published helpers retain their own attribution.

The motivating original is H. Jacquet, I. I. Piatetski-Shapiro and
J. Shalika, *Automorphic forms on GL(3) I*, Ann. of Math. (2) 109 (1979),
169–212, registered source `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
The source text on printed pp.181–183 and page images on pp.181–182
were read; these are one-based PDF pp.14–16 and pp.14–15 respectively.
The p.181 finite-operator argument starts with a smooth representation.
Lemma (2.2.1) on p.182 applies it to coordinate quotients and requires
uniform small-coordinate control. The present theorem is an internal
derived bridge from the stated scalar local-constancy hypothesis, rather
than a theorem stated separately by JPS. Its implemented proof derives
the common kernel and the representative uniformity instead of assuming
smoothness.

No matching source-specific erratum was found in the available project,
Library, and literature material checked; this is a bounded check, not
a claim that no erratum exists. The later uniform dilation expansion for
all `|b| ≤ 1` and the full JPS decomposition remain separate results.
