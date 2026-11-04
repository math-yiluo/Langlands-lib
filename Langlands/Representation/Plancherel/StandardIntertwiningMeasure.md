# Measure rescaling and the actual diagonal standard integral

This module proves the effect of finite measure rescaling on the actual
standard integral and constructs the diagonal integral on the entire source
normalized induction. Its value is the total-mass multiple of the original
function; for a probability quotient measure it returns that function.

The source is Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), IV.1, printed pp.277–278 (PDF pp.43–44).
There the integral over `(U ∩ U') \ U'` is defined by absolute convergence
against every smooth contragredient functional and a representing vector in
the original carrier. The results here are internal deductions from that
definition and the previously constructed actual quotient integrand. They
are not separately numbered assertions of the article.

## Objects and hypotheses

The general weak-integral lemmas are in
`Langlands.HarmonicAnalysis.SmoothWeakIntegral`. Their measurable source,
group and carrier have independent universes. The group has a topology for
the smooth-contragredient tests; the carrier is an algebraic complex module,
with no topology or completeness assumption.
No smooth-dual separation hypothesis is needed for these integral relations.

The standard-integral results are in
`Langlands.Plancherel.StandardIntertwining`. Their inputs are:

- A locally compact nonarchimedean group `G`, with actual subgroups `P`, `M`,
  `U` and a semidirect decomposition `h : IsSemidirectDecomposition P M U`.
- Closed source radical `U`, an arbitrary target subgroup `U'`, and the
  canonical complex smooth representation `A` of `M`. The group and carrier
  universes remain independent.
- A measurable structure on the actual left quotient
  `QuotientSpace (U := U) U' = LeftQuotient (U.subgroupOf U')`, and a measure
  `ν` on it. The intersection need not be normal.

The source is the actual positive Levi-normalized induction
`(DynamicNormalization.leviTwistedInductionFunctor h hU).obj A`.
The imported `domain` consists of its functions for which every evaluation
point has scalar absolute convergence and a representing vector in `A`.
These are properties proved or transported here, not assumed for the whole
source.

Measure rescaling uses `c : ℝ≥0`, so the scalar is finite. Domain equality and
the selected-operator comparison require `c ≠ 0`. No Haar, right-invariance,
Borel or quotient-compatibility condition is needed for this comparison.
Each selected-operator result additionally displays closedness of `M`, which
supplies compact-open cofinality and smooth-dual separation through the
imported construction.

## Finite measure rescaling

`SmoothWeakIntegral.HasIntegral.smul_measure_nnreal` proves

`HasIntegral ρ μ F v → HasIntegral ρ (c • μ) F ((c : ℂ) • v)`.

Here `(c : ℂ)` denotes the real coercion followed by the complex coercion.
For each original smooth functional the proof preserves scalar
integrability under finite rescaling and uses the genuine scalar
measure-rescaling integral formula. It evaluates the scaled representing
vector by linearity.

`integrable_smul_measure_nnreal_iff` proves exact preservation of scalar
convergence together with representability when `c ≠ 0`. The reverse
direction rescales by `c⁻¹`, using its explicitly scaled representing
vector. The forward construction also allows `c = 0`, but no domain
equality at zero is claimed.

`StandardIntertwining.HasIntegral.smul_measure_nnreal` applies this result at
every `g`. `domain_smul_measure` identifies the two actual submodules.
`operator_smul_measure` compares the selected operators on precisely the
same original induced function, using that equality to prove membership in
the rescaled domain. The output for `c • ν` is `g ↦ (c : ℂ) • Jν(f)(g)`.
Its proof rescales the selected operator's integral specification and
applies uniqueness.

## Diagonal integral on the full source

For the diagonal case the target subgroup is literally `U`. A measurable
structure and a measure `ν₀` on `QuotientSpace (U := U) U` are supplied
explicitly. The finite-measure and probability assumptions below concern
that actual measure. The module does not infer its mass from arbitrary
chosen Haar measures.

`integrand_diagonal` proves that the descended integrand is the constant
function with value `f(g)`. Quotient induction reduces this to the
representative identity `f(u g) = f(g)`, which is the imported source
unipotent invariance.

`SmoothWeakIntegral.hasIntegral_const` proves that a constant function has
weak integral `(μ univ).toReal • v` for any finite measure. Its proof applies
scalar constant integrability and the constant integral formula to every
smooth functional, then uses linearity.

`hasIntegral_diagonal` combines these two facts, giving every normalized
induced function the representing function
`g ↦ ((ν₀ univ).toReal : ℂ) • f(g)`.
`domain_diagonal` consequently proves `domain h hU U A ν₀ = ⊤`.
`operator_diagonal` identifies the restricted selected operator with that
function, and `operator_diagonal_probability` simplifies its mass to one
under `IsProbabilityMeasure ν₀`.

`diagonalOperator` is the resulting linear map from the **entire** source
normalized induction to `G → A`. It is constructed by sending each input
to its proved domain membership and applying the existing actual selected
operator. It is not defined by stipulating the desired identity.
`diagonalOperator_spec` proves the original smooth-dual scalar integral
relation. `diagonalOperator_eq` and `diagonalOperator_probability` identify
its value respectively with the total-mass multiple and the original
induced function, as functions on `G`.

## Scope

These are generic actual subgroup and measure constructions. They impose no
restriction on the characteristic of a local field and make no rational-point
realization claim. Full-source convergence is proved here for the diagonal
case with finite quotient measure. Convergence cones for distinct
parabolics, reductive target-modulus comparison, target induced-space
packaging for the general integral, rational continuation, composition
scalars and Plancherel remain separate obligations. In particular, the
module does not prove Waldspurger IV.1.1.
