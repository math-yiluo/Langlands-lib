# Injectivity of the degree-two reduced coproduct

Module `Langlands.AbelianScheme.FieldH2PrimitiveInjectivityProof`.

The theorem `Langlands.AbelianScheme.fieldH2PrimitiveInjectivity.{u}` proves exactly
[`Langlands.AbelianScheme.FieldH2PrimitiveInjectivityStatement.{u}`](../AlgebraicGeometry/Picard/FieldH2PrimitiveInjectivityStatement.md).
For every field `K : Type u` and abelian scheme `A` over `Spec K`, the map

```text
μ* − p₁* − p₂* : H²(A, O_A) → H²(A ×_K A, O_(A ×_K A))
```

is injective. These are the actual right-derived structure-sheaf cohomology objects.
Each pullback is `relativeCohomologyPullback` followed by the cohomology map of
`Langlands.Scheme.Modules.pullbackUnitIso`. The theorem has no additional premise
or restriction on the characteristic or dimension.

## Implemented proof

The proof applies
`Langlands.AbelianScheme.fieldH2PrimitiveInjectivity_of_exteriorCoproductComparison`
from the [comparison statement module](../AlgebraicGeometry/Picard/FieldH2ExteriorCoproductComparisonStatement.md)
to the published theorem
`Langlands.AbelianScheme.fieldH2ExteriorCoproductComparison` from
[`FieldH2ExteriorCoproductComparisonProof`](FieldH2ExteriorCoproductComparisonProof.md).
Both use the same field universe `u`, so this application discharges the entire
comparison premise.

The reduction uses the simultaneous linear equivalences `e` and `κ` supplied by
the comparison. In the middle coordinate of `κ`, the two projection pullbacks
vanish and multiplication pullback becomes
`exteriorPower.toTensorPower K H¹(A, O_A) 2 ∘ e`. Equality of reduced pullbacks
therefore gives equality after this composite. The tensor map is injective on
the exterior square of a vector space, by
[`exteriorPowerToTensorPower_injective`](../LinearAlgebra/ExteriorPowerTensorInjectivity.md);
injectivity of `e` then gives equality of the original classes. This argument
requires no division by two and applies in characteristic two.

## Provenance and independence

This module is an internal derived application of published results and adds no
external mathematical input. The target and comparison statements record their
original-source dictionary, and the imported proof modules describe the
implemented geometric comparison.

The comparison is proved using canonical creation and contraction operators and
the independent first-cohomology dimension theorem. Neither that proof nor this
application uses `ArtinianPrimitiveLineBundleLiftingStatement`,
`PicardZeroArtinianLiftingStatement`, `FiniteTypeDualSchemeGeometryStatement`,
`RelativeDualSchemeGeometryStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` or
`SmoothFamilyAbelianRepresentabilityStatement`, their proofs, or results proved
through them. The comparison does not depend on this primitive-injectivity
theorem. The target's Lean/Markdown pair and every pair in its import closure
are unchanged.
