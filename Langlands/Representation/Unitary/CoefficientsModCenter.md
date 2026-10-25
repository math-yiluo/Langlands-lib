# Invariant-form coefficients on the actual central quotient

Author: Worker 386.

This internal comparison connects the Library's smooth-dual coefficient norms
to coefficients of an actual invariant positive Hermitian form, and connects its
universal Borel Haar predicate to any fixed Borel Haar measure. All coefficient
norms remain functions on the actual quotient by the full group center.

## Form coefficients

For an algebraic complex representation `ρ` of a topological group `G`,
`InvariantPositiveForm.coefficientNorm b c w v` is the existing descended norm
`c.coefficientNorm (b.rightFunctional w) v`. Its value on the class of `g` is
exactly `‖b.inner w (ρ g v)‖`, as stated by `coefficientNorm_mk`.
Well-definedness on `G / Z(G)` uses the actual scalar action and unit norm of
`c : UnitaryCentralCharacter ρ` through the published descent construction.
`coefficientNorm_eq` proves independence of the choice of this witness.
No complex-valued descent of the coefficient is asserted.

`forall_memLp_coefficientNorm_iff` compares all smooth-dual coefficients with all
form coefficients for every measure and every extended nonnegative exponent.
It assumes admissibility and compact-open cofinality. In the forward direction,
`b.toSmoothDual` makes `b.inner w (-)` an actual smooth-dual functional.
In the reverse direction, the published
`InvariantPositiveForm.toSmoothDual_surjective` represents any smooth functional
by some `w`. Substitution then identifies the functions exactly.
The finite-dimensional Riesz argument lies in that imported theorem on compact
open fixed spaces; the incoming representation carrier has no norm, topology
or finite-dimensionality assumption.

`InvariantPositiveForm.isSquareIntegrableModCenter_iff` applies that equivalence
at exponent two and retains the admissibility and unitary central-character
clauses of the existing analytic predicate. It compares the two coefficient
formulations for the same specified Haar measure on the same Borel quotient.

## The p-adic fixed-measure comparison

For arbitrary `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData`, every matrix rank `n : ℕ`, and an arbitrary independent
carrier universe `uV`,
`PadicField.TopologicalData.isSquareIntegrable_iff_fixedHaar` proves that
`T.IsSquareIntegrable ρ` is equivalent to
`IsSquareIntegrableModCenter ρ μ` for each Borel Haar measure `μ` of the actual
central quotient. The measurable structure is exactly
`T.centralQuotientMeasurableSpace n`; the field topology is exactly `T.topology`.

The proof uses `glBlockCentralQuotientTopology` to obtain the topological group,
local compactness and second countability of that quotient. The forward direction
specializes the universal measure quantifier. For the reverse direction, the
published `haarMemLpInvariant` transfers each coefficient's `MemLp` membership
from `μ` to an arbitrary Borel Haar measure `ν`, retaining the same admissibility
and central-character witness. The imported proof already supplies Haar
uniqueness and finite measure scaling; they are not assumed as extra comparison
data or reimplemented here.

`isSquareIntegrable_iff_formCoefficients` combines this result with the preceding
Hermitian comparison and the published
`GeneralLinear.compactOpen_cofinal F T n`. Thus the exact universal-Haar analytic
predicate is equivalent to admissibility and existence of an actual unitary
central character for which all form-coefficient norms belong to `L²` for the
chosen Haar measure.

These results concern vectors in the original algebraic smooth representation.
They do not extend square-integrability to arbitrary vectors of a completion,
construct an embedding into a regular representation, recover smooth vectors,
or prove mirabolic restriction or genericity.

## Provenance

This module is derived from the actual Library form, smooth-dual, descended-norm
and p-adic topology constructions, using their proved comparison and Haar
normalization theorems. The imports are `Unitary.HermitianDual`,
`Classification.Tempered`, `Category.Contragredient`, `Analysis.HaarLpProof`,
and `Group.GL.CentralQuotientTopologyProof`, under `Langlands`.
It adds no literature assertion as a hypothesis and preserves every existing pair.
