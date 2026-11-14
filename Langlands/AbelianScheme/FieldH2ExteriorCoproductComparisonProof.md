# The degree-two exterior and canonical coproduct comparison

Module `Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonProof`.

The theorem `Langlands.AbelianScheme.fieldH2ExteriorCoproductComparison.{u}` proves exactly
`Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonStatement.{u}`. For every field
`K : Type u` and abelian scheme `A` over `Spec K`, it gives simultaneous `K`-linear
equivalences

```text
e : H²(A, O_A) ≃ₗ[K] ⋀[K]^2 H¹(A, O_A)
κ : H²(A ×_K A, O_(A ×_K A))
      ≃ₗ[K] H²(A, O_A) × (⨂[K]^2 H¹(A, O_A)) × H²(A, O_A).
```

For the canonical projections `p₁`, `p₂` and group multiplication `m`, these satisfy

```text
κ(p₁* x) = (x, 0, 0)
κ(p₂* x) = (0, 0, x)
κ(m* x)  = (x, exteriorPower.toTensorPower K H¹(A, O_A) 2 (e x), x).
```

The cohomology objects are the actual right-derived relative global sections of the
structure modules. Each pullback is the canonical cohomology pullback followed by the
cohomology map of `pullbackUnitIso`, exactly as in the target. The same witnesses `e` and
`κ` satisfy all three formulas. There is no characteristic restriction, algebraic
closure assumption, chosen basis premise, or positive-dimension premise.

## Implemented proof

The Lean proof applies
`fieldH2ExteriorCoproductComparison_of_H1Dimension` from
[`CanonicalCAR`](CanonicalCAR.md) to the theorem
`fieldStructureSheafH1Dimension` from
[`FieldStructureSheafH1DimensionProof`](FieldStructureSheafH1DimensionProof.md).
Both are universal in the same field universe `u`; no hypothesis remains.

The first input constructs the creation and contraction operators on actual
structure-sheaf cohomology. Multiplication pullback, degree-one primitivity, and the two
axis slant formulas give their anticommutation relation on every positive input degree.
A finite basis of `H¹` and its coordinate functionals then give `canonicalCARData`.
[`DegreeTwoComparisonFinal`](DegreeTwoComparisonFinal.md) uses the supplied equality
`dim H¹(A, O_A) = dim A`, together with geometric cohomology vanishing, to bound this
creation-contraction family. Bounded contraction detection proves that cup squares
vanish in every characteristic. The existing comparison assembly combines this
alternation with the canonical degree-two sum-map injectivity to obtain both
equivalences and all three pullback formulas.

The second input proves finite-dimensionality and the required dimension equality over
every field. It combines the published upper bound with a lower bound from a minimal
Picard deformation hull, the finite Mumford agreement locus, and local commutative
algebra. Its paired Markdown describes this route and its helper modules.

## Provenance and independence

This module is an internal derived application of those two theorems. It adds no
external mathematical input. The target's paired Markdown records the original
exterior-coproduct dictionary; the proof explanations in the imported modules describe
the implemented route.

The proof does not use `ArtinianPrimitiveLineBundleLiftingStatement`,
`PicardZeroArtinianLiftingStatement`, `FiniteTypeDualSchemeGeometryStatement`,
`RelativeDualSchemeGeometryStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` or
`SmoothFamilyAbelianRepresentabilityStatement`, their proofs, or results proved
through them. The dimension input uses formal deformation machinery and the finite
agreement locus without assuming these representability conclusions.

The proof also does not use a proof of `FieldH2PrimitiveInjectivityStatement`, or a
result depending on such a proof. The target module imports that proposition and proves
the reverse conditional implication from the comparison to primitive injectivity;
this proof does not apply that implication. The injectivity used in the comparison
assembly is the independently established canonical degree-two sum-map injectivity.
The target's Lean/Markdown pair and every pair in its import closure are unchanged.
