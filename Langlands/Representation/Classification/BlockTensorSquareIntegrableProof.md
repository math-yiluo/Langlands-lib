# Square-integrability of actual GL block tensors

Author: Worker 158.

`Langlands.glBlockTensorSquareIntegrable` proves exactly the closed proposition
`Langlands.GLBlockTensorSquareIntegrableStatement.{uF,uV}` in
[BlockTensorAnalyticStatement](BlockTensorAnalyticStatement.md).
The field universe `uF` and representation carrier universe `uV` remain
independent, in that order. The theorem has no outer premises.

For every prime, actual p-adic field `F`, supplied compatible topology `T`,
positive total rank, block shape `B`, and family of irreducible admissible
complex GL block representations `ρ i`, it proves both implications of

```text
(∀ i, T.IsSquareIntegrable (ρ i)) ↔
  ∀ Borel measurable-space realizations on B.Levi F.Carrier / its full center,
    ∀ Haar measures μ,
      IsSquareIntegrableModCenter (B.blockTensor ρ) μ.
```

The tensor is the actual `B.blockTensor ρ = FiniteTensor.external ρ`, with
the supplied product Levi topology. The conclusion quantifies over every
Borel realization and Haar measure on the quotient by the full actual Levi
center. It tests all vectors and all actual smooth-dual functionals. Factor
square-integrability already includes every Haar measure on its canonical
Borel central quotient. Admissibility retains the Library's all-open
convention. There is no countability restriction on the carriers or chosen
central character, Haar normalization, or invariant form.

The implemented proof is the exponent-two specialization of the published
closed theorem `Langlands.glBlockTensorLp` from
[BlockTensorLpProof](BlockTensorLpProof.md). After introducing the exact target
quantifiers, it installs `T.topology`, `T.leviTopology B`, and
`T.leviTopologicalGroup B`, then applies that theorem with real exponent
`r = 2` and the reflexive bound `2 ≤ 2`.

In the forward direction, `T.isLp_two_iff` converts each factor's
square-integrability into its fixed-exponent `T.IsLp` condition. The common
comparison gives the tensor's fixed-exponent condition under each supplied
measurable-space, Borel-space, Haar-measure, and Haar-instance binder.
`isLpModCenter_two_iff` converts it to square-integrability there. In the
reverse direction, the same generic equivalence converts the assumed tensor
condition under every one of those binders. Reflection in the common theorem
gives every factor's `T.IsLp` condition, and `T.isLp_two_iff` converts each back.
Both intrinsic exponent-two identifications are proved in
[LpModCenter](LpModCenter.md); they retain admissibility, the existential
unitary character, and all smooth coefficients.

This is internally derived mathematical content. It introduces no new
literature assertion beyond the analytic conventions and derived product
target documented in the unchanged `BlockTensorAnalyticStatement` pair.
The common proof supplies the full-center quotient and Haar transport,
central-character assembly and reflection, admissible smooth-dual
surjectivity, finite-sum coefficient closure, product integration, and
nonzero-factor reflection. Those results are imported by Lean name rather
than reproved here. No downstream induction, classification, or uniqueness
result is assumed. The target pair and all its imports are unchanged.
