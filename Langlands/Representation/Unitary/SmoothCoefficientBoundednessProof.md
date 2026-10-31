# Proof of boundedness for smooth-dual coefficients

Authors: Worker 480 (Lean implementation and original explanation) and
Worker 252 (submission, import-closure and independence audit).

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

## Independence audit

The task requires that neither this proof nor any prerequisite depends,
directly or transitively, on the following tasks, their mathematical
conclusions, proof successors or downstream consequences. None of them is
imported or used as a mathematical input, since the closure above consists of
generic smooth-representation modules and the argument is Cauchy–Schwarz plus
invariance:

- Individual special-head/reverse-socle existence
  `67279e36-f3c2-42e3-9302-11729784042e`.
- Individual segment-socle/reverse-head existence
  `4ca79bbd-589e-476b-9f65-661e799984b5`.
- Analytic segment classification
  `aca8805b-054f-4d56-8045-12db7f623404`.
- Forward special square-integrability,
  `SegmentSpecialEssentialSquareIntegrability`, and
  `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`.
- Multisegment special-head exhaustion
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`.
- Ordered strong-head existence
  `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`.
- Quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`.
- Ordered conversion `8252833d-c269-41a9-824c-5879e531b23b`.
- Tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c`.
- `SquareIntegrableLanglandsClassification` and
  `1cb45da2-7007-4351-a694-594fb148b8d1`.
- Square-integrable exhaustion
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`.
- Regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`.
- Special-head product irreducibility
  `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`.
- `GenericSegmentProductUniqueness` and
  `30341ae4-65f2-4a0e-9283-763db01a409e`.
- `OrderedMultisegmentSocleExistence` and
  `23189526-80b0-4828-a6d4-7ebec2cbeef5`.
- `MultisegmentSocleExhaustion` and
  `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`.
- `SegmentSocleProductIrreducibility` and
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`.
- Adjacent socle commutation
  `e3634665-571b-4852-9f4c-bab8a1053434`.
- `SegmentFullJacquetFormula`, its statement/successor-arrangement task
  `ed48ae06-964c-4c84-9e62-978f5a953ca7`, and its exact proof successor.
- `SegmentHeadJacquetFormula` and
  `55ad1e10-62d8-46b7-a081-909ef0056426`.
- `SegmentSocleJacquetFormula` and
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034`.
- `SegmentSpecialJacquetExponentNormFormula` and
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`.

The full-formula consumer's additional restrictions also hold for this proof
and for every module in its closure. No derivative formula is assumed (Ze80
§3.5 or §9.6, or BZ77 derivative results), and neither is a segment product
irreducibility criterion (Ze80 4.2 or 9.7), an analytic or
square-integrability result (Ze80 9.3), or a classification or exhaustion
theorem. In particular, Ze80 Theorem 4.2's linked-pair converse is not used,
so no circular route to Proposition 1.11 arises. The proof adds no new
prerequisite modules, and the shared lower constructions it reuses are the
generic modules listed above.

## Operator derivative clarification: condition-by-condition audit

The trusted operator clarification (correspondence
`bd71b9185aab5d6eafffb7891bd3a3ca`, response to request
`a8463ee15d57588c8de10306748b2538`) permits a fully proved route through
BZ77's general derivative theory. This proof does not use that permission,
because it uses no derivative theory at all.

1. Only BZ77's general derivative theory, not Ze80 §3.5 or §9.6: no
   derivative result of either kind is used.
2. Every derivative result must be proved, accepted and published: there is
   no derivative result to check.
3. The closure must exclude every task and conclusion listed under
   Independence and the segment-socle part of
   `8e5b4563-0365-41c7-b134-70f2a0b36292`: the 14-module closure above
   contains none of them, and nothing from either part of `8e5b4563`.
4. Reuse of the derivative infrastructure (`d3e94f0f`, `dfae49d8`,
   `2206daa6`): not applicable, since no derivative infrastructure is needed
   or duplicated.
5. This section is the audit record.
