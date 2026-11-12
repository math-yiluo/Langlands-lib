# Finite-support fixed vectors of compact induction

`compactFixedEvaluationEquiv` identifies the `K`-fixed vectors of the original
`CompactFunctions P σ` with

```text
Π₀ q : P \ G / K, fixedVectors σ (P ∩ q.out K q.out⁻¹).
```

Here `G` is a topological group, `P` is an arbitrary subgroup, `σ` is a
representation of `P` over a commutative ring `R`, and `K` is a compact open
subgroup of `G`. The expression on the right is Lean's dependent direct sum,
`DFinsupp`; the conjugate intersection is the published `conjOpenSubgroup`.
Evaluation uses Mathlib's chosen representative `q.out` of each double coset.
The inverse is a finite sum of the original compact double-coset sections,
with the chosen vector as value at its representative.

The coefficient ring, group, and representation carrier have independent
universe parameters `uR`, `uG`, and `uV`. There is no finiteness or compactness
assumption on `P \ G / K` or `P \ G`. Neither closedness of `P`, local
compactness of `G`, nor smoothness of `σ` is needed. Compactness of `K` is
used for constructing the inverse sections; the evaluation map and its
injectivity require only that `K` is open.

The construction and its proof use the following declarations.

- `compactFixedToSmooth` forgets compact support while preserving the fixed
  vector condition.
- `compactFixedEvaluationAt` evaluates at one point, with values in its
  coefficient fixed space, by the published `eval_mem_fixedVectors`.
- `compactFixedEvaluation_finite` supplies a finite set of double cosets
  outside which evaluation vanishes. It takes a finite subcover of the
  section's actual compact quotient support by the open images of `x K`.
  Thus `compactFixedEvaluation` lands in `DFinsupp` and is linear by
  pointwise evaluation.
- `compactFixedEvaluation_injective` uses covariance and right `K`
  invariance to recover all values from those at the representatives.
- `compactFixedSection` is the published `compactDoubleCosetSection`,
  bundled as a fixed vector of the original compact induction.
  `compactFixedEvaluation_section` proves that its image is
  `DFinsupp.single q v`, using `fixedDoubleCosetSection_eval_self` and
  `fixedDoubleCosetSection_eval_of_ne`.
- `compactFixedSectionLinear` bundles the linear dependence on `v`.
  Linearity follows from the preceding coordinate identity and injectivity.
  `compactFixedSectionSum` applies `DFinsupp.lsum` to these linear maps.
- `compactFixedEvaluation_sectionSum` proves that evaluation after summing
  sections is the identity by checking single-coordinate vectors.
  This identity and evaluation injectivity give
  `compactFixedEvaluationEquiv`; its two application lemmas identify the
  forward map and explicit inverse.

This is derived infrastructure for the fixed-vector argument in Renard
III.2.6, printed pp.76–77 / PDF pp.82–83, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It generalizes the finite-transversal construction in the published
`FixedVectorModel`, using `CompactLocalSection` and
`CompactQuotientProof`. Renard's comparison theorem is a separate
obligation; this module supplies the compact-induction fixed-vector model
without asserting the tensor comparison.
