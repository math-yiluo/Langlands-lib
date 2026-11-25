# Proof of boundedness for smooth-dual coefficients

## Result

`Langlands.admissibleUnitarizableSmoothCoefficientsBounded G V` proves
`Langlands.AdmissibleUnitarizableSmoothCoefficientsBounded.{uG,uV} G V` for
`(G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]` and
`(V : Type uV) [AddCommGroup V] [Module ℂ V]`, with independent group and
carrier universes and no further hypotheses. For every complex
representation `ρ` of `G` on `V` for which compact open subgroups are cofinal
among open subgroups, and which is admissible and unitarizable, it gives, for
every smooth-dual functional `ℓ` and vector `v`, a real `C ≥ 0` with
`‖smoothDualPairing ρ ℓ (ρ g v)‖ ≤ C` for all `g : G`. The bound depends on
`ℓ` and `v`. No norm or topology on `V`, finite-dimensionality of `V`,
irreducibility or completeness is assumed.

## Proof

Unitarizability supplies an invariant positive definite Hermitian form `b`
(`InvariantPositiveForm ρ`, linear in its second variable). The published
`InvariantPositiveForm.toSmoothDual_surjective`, which needs exactly
cofinality of compact open subgroups and admissibility, gives a vector `u`
whose smooth functional `w ↦ b(u, w)` is `ℓ`. After this substitution the
coefficient is `b(u, ρ(g)v)`.

Inside the proof only, the inner-product core of `b` provides a normed group
and inner-product space structure on `V`, with `‖x‖ = √(Re b(x, x))`. These
local instances exist only to construct the real witness; the statement
mentions no norm on `V`. Mathlib's Cauchy–Schwarz inequality
`norm_inner_le_norm` gives

`‖b(u, ρ(g)v)‖ ≤ ‖u‖ ‖ρ(g)v‖ = ‖u‖ ‖v‖`.

The equality `‖ρ(g)v‖ = ‖v‖` is proved by unfolding both norms to
`√(Re b(·, ·))` and applying the invariance `b(ρ(g)v, ρ(g)v) = b(v, v)`.
Hence `C = ‖u‖ ‖v‖` is a nonnegative bound independent of `g`. No
completeness or infinite-dimensional Riesz theorem is used: surjectivity onto
the smooth dual comes from finite-dimensional compact-open fixed spaces.

## Convenience theorem and obstruction corollaries

All three keep the smooth-dual functional and the admissibility and
cofinality hypotheses. None asserts boundedness for arbitrary algebraic
functionals.

- `Langlands.IsUnitarizable.smoothCoefficient_bounded` restates the
  conclusion for a given `ρ`, with the unitarizability hypothesis first,
  followed by cofinality, admissibility, `ℓ : SmoothDual ρ` and `v`.
- `Langlands.not_isUnitarizable_of_unbounded_smoothCoefficient` is the
  contrapositive: if, for one smooth functional `ℓ` and vector `v`, every real
  `C` is exceeded by `‖smoothDualPairing ρ ℓ (ρ g v)‖` for some `g`, then `ρ`
  is not unitarizable.
- `Langlands.not_isUnitarizable_of_unbounded_smoothCoefficient_sequence` has
  the same conclusion when the exceeding values occur along a sequence
  `g : ℕ → G`; no topological condition on the sequence is required.

These corollaries do not show that any particular induced coefficient is
unbounded, nor that a given algebraic functional is smooth. No explicit
induced-coefficient calculation or reducibility theorem is part of this
module.

## Provenance

The result and its proof are internal and derived from existing Library
results; no literature theorem is formalized here beyond the standard
argument that matrix coefficients of a unitary representation are bounded by
Cauchy–Schwarz. The direct imports are the target statement module and
`Langlands.Representation.Unitary.HermitianDual`. Mathlib supplies
Cauchy–Schwarz and the inner-product structures built from an algebraic
positive form.

## Project import closure

The complete project-module import closure of this module, recomputed from the
Library at commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11`, has 14 modules:

- `Langlands.Representation.Compact.Definitions`
- `Langlands.Representation.Compact.FiniteMean`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Smooth.Contragredient.CompactDualityProof`
- `Langlands.Representation.Smooth.Contragredient.CompactDualityStatement`
- `Langlands.Representation.Smooth.Contragredient.Definitions`
- `Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`
- `Langlands.Representation.Unitary.Basic`
- `Langlands.Representation.Unitary.HermitianDual`
- `Langlands.Representation.Unitary.SmoothCoefficientBoundednessProof`
- `Langlands.Representation.Unitary.SmoothCoefficientBoundednessStatement`

These modules contain only algebraic representations, smoothness and
admissibility, the smooth dual and contragredient, compact-open orbit
averaging, duality of finite-dimensional compact-open fixed spaces, and
invariant positive forms. None of them mentions segments, Jacquet modules,
derivatives, square-integrability, classification, exhaustion, socles or
irreducibility criteria. The development check of this module reported only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Independence

Neither this proof nor any module in its closure depends, directly or
transitively, on the following results, their mathematical conclusions,
their proofs or their downstream consequences. None of them is
imported or used as a mathematical input, since the closure above consists of
generic smooth-representation modules and the argument is Cauchy–Schwarz plus
invariance:

- Individual special-head/reverse-socle existence.
- Individual segment-socle/reverse-head existence.
- Analytic segment classification.
- Forward special square-integrability,
  `SegmentSpecialEssentialSquareIntegrability`.
- Multisegment special-head exhaustion.
- Ordered strong-head existence.
- Quotient coverage.
- Ordered conversion.
- Tempered uniqueness.
- `SquareIntegrableLanglandsClassification`.
- Square-integrable exhaustion.
- Regular exhaustion.
- Special-head product irreducibility.
- `GenericSegmentProductUniqueness`.
- `OrderedMultisegmentSocleExistence`.
- `MultisegmentSocleExhaustion`.
- `SegmentSocleProductIrreducibility`.
- Adjacent socle commutation.
- `SegmentFullJacquetFormula` and its proof.
- `SegmentHeadJacquetFormula`.
- `SegmentSocleJacquetFormula`.
- `SegmentSpecialJacquetExponentNormFormula`.

The following also holds for this proof
and for every module in its closure. No derivative formula is assumed (Ze80
§3.5 or §9.6, or BZ77 derivative results), and neither is a segment product
irreducibility criterion (Ze80 4.2 or 9.7), an analytic or
square-integrability result (Ze80 9.3), or a classification or exhaustion
theorem. In particular, Ze80 Theorem 4.2's linked-pair converse is not used,
so no circular route to Proposition 1.11 arises. The proof adds no new
prerequisite modules, and the shared lower constructions it reuses are the
generic modules listed above.

## Derivative theory

This proof uses no derivative theory at all.

1. No derivative result is used, neither from BZ77's general derivative
   theory nor from Ze80 §3.5 or §9.6.
2. There is therefore no derivative result whose proof needs checking.
3. The 14-module closure above contains none of the results listed under
   Independence, and no segment-socle or cuspidal-derivative result.
4. No derivative infrastructure is needed or duplicated.
