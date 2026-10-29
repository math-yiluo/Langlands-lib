# Square-integrability of quotients of the maximal layer: proof

Author: Worker 728.

This module proves the published statement of
[`WeakCriticalTopLayerL2Statement`](WeakCriticalTopLayerL2Statement.md):

```text
theorem Langlands.glWeaklyCriticalTopLayerL2 :
    GLWeaklyCriticalTopLayerL2Statement.{uF, uV, uW}
```

The field universe `uF`, the source carrier universe `uV` and the quotient
carrier universe `uW` stay independent. The statement is imported by its Lean
name and is not modified. The theorem has no hypotheses.

## Implemented proof

The proof is one application of two theorems:

1. `glWeaklyCriticalTopLayerL2_of` (module
   [`WeakCriticalTopLayerL2Reduction`](WeakCriticalTopLayerL2Reduction.md))
   proves the target from the dual-opposite product-Levi square-integrability
   criterion `GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement.{uF, uW}`.
   It contains the coordinate transport, the index comparison for quotients of
   the maximal layer, and the use of weak criticality; see its Markdown.
2. `glProductLeviDualOppositeSquareIntegrableSufficiency` (module
   [`ProductLeviDualOppositeSquareIntegrableSufficiencyProof`](../Classification/ProductLeviDualOppositeSquareIntegrableSufficiencyProof.md))
   proves that criterion. It reduces it to the upper core form, which is
   proved in
   [`ProductLeviSquareIntegrableSufficiencyProof`](../Classification/ProductLeviSquareIntegrableSufficiencyProof.md)
   by the strict chamber bound and an `L²` summation over Cartan cells.

Applying the first theorem to the second, at the universes `uF` and `uW`,
gives the target. The final theorem type contains no added hypothesis.

## Provenance

Mathematically this is the analytic part of the proof of Silberger 1979,
Corollary 4.5.11 (printed pp.189–190): Theorem 4.5.10 (the `L²` criterion) is
applied to a quotient of the maximal layer of Corollary 2.4.2, and weak
criticality excludes the boundary case. The sources and the derivation of the
statement are recorded in the statement's Markdown and in the Markdown of the
imported modules.

## Independence

The import closure contains the proposition definitions
`GLWeaklyCriticalDiscreteSeriesSupportStatement`,
`GLWeaklyCriticalPairMinimalityStatement`,
`GLWeaklyCriticalTemperedRefinementStatement` and
`GLTemperedDiscreteSeriesSupportStatement` only as definitions, through the
statement modules `WeakCriticalStatement` and `TemperedSupportStatement`. No
proof of these propositions, and no exhaustion, unitarity, genericity or
equal-exponent grouping theorem, is used. Tasks `3a43d7be…` and `535b7e03…`
have no artifacts, so no imported result consumes them.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
