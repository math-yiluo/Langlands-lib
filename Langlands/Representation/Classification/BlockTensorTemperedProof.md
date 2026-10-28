# Analytic temperedness of actual GL block tensors

Author: Worker 403.

`Langlands.glBlockTensorTempered` proves the exact closed proposition
`Langlands.GLBlockTensorTemperedStatement.{uF, uV}` from
[BlockTensorAnalyticStatement](BlockTensorAnalyticStatement.md).
The field and representation carrier universes are independent.

For every prime, p-adic field, supplied compatible topology, positive total
rank and actual block shape, and every family of irreducible admissible block
representations, the theorem proves

```text
(∀ i, T.IsTempered (ρ i)) ↔
  ∀ Borel realizations on B.Levi F.Carrier / its full center,
    ∀ Haar measures μ, IsTemperedModCenter (B.blockTensor ρ) μ.
```

The representation is the actual external tensor, with all its vectors and
all its smooth-dual functionals. The theorem retains the target's all-open
admissibility hypotheses, supplied product Levi topology, full group center,
and every Borel and Haar quantifier.

This proof specializes the published common finite-exponent comparison
`Langlands.glBlockTensorLp` from
[BlockTensorLpProof](BlockTensorLpProof.md), authored by Worker 450, at
`r = 2 + ε` for every real `ε > 0`. The inequality `2 ≤ 2 + ε` follows from
nonnegativity of `ε`. It uses the two compatibility lemmas in
[TemperedLpProof](TemperedLpProof.md), authored by Workers 403 and 363:
`Langlands.isTemperedModCenter_iff_forall_isLp` for a fixed quotient Haar
measure and `T.isTempered_iff_forall_isLp` for each canonical GL factor.

For preservation, fix any Borel realization and Haar measure on the actual
Levi central quotient. The generic compatibility lemma reduces temperedness
of the tensor to its fixed-exponent condition for every positive `ε`.
The canonical GL compatibility lemma gives that condition on each tempered
factor at `2 + ε`, and the forward common comparison gives it on the tensor
for the supplied measure.

For reflection, fix a factor and a positive `ε`. The tensor's temperedness
for every Borel Haar realization gives its fixed-exponent condition for
every such realization by the generic compatibility lemma. The reverse
common comparison gives the canonical all-Haar fixed-exponent condition on
every factor. Applying the canonical GL compatibility lemma to all positive
`ε` proves the chosen factor tempered.

The compatibility proof handles the existential central character uniformly:
it chooses one witness at `ε = 1` and transfers the other exponent conditions
using equality of the descended coefficient norms. The common comparison
supplies the coefficient decomposition, product integration, reflection and
Haar transport. Those results are imported by Lean name; this specialization
only interchanges universal quantifiers and applies their proved equivalences.

The provenance is an internal derivation from these published results and the
unchanged analytic target. No new original-literature assertion is used.
The proof adds no premise to the closed target, imposes no carrier countability
or Haar normalization, and invokes no downstream induction or classification
theorem.
