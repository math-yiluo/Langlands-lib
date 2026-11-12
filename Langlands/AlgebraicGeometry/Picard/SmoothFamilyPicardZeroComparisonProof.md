# Smooth-family algebraic triviality and translation invariance

`Langlands.AbelianScheme.smoothFamilyPicardZeroComparison` proves the exact
published proposition
`Langlands.AbelianScheme.SmoothFamilyPicardZeroComparisonStatement.{u}`.
The universe `u` is arbitrary. The theorem has no additional premise.

For every algebraically closed field `K : Type u`, abelian scheme `A` over
`Spec K`, and actual line bundle `L` on its total space, its first conjunct is

```text
IsAlgebraicallyTrivialViaSmoothFamily A L
  ↔ Langlands.GroupScheme.IsTranslationInvariant A.toGrp L.
```

Its other three conjuncts are the published geometric-fibre, rigidified-family
and rigidified-isomorphism-class comparisons. They retain arbitrary bases and
test schemes in the same universe, the actual `fibreLineBundle` and
`familyLineBundle`, and the existing quotient by actual rigidified isomorphism.

## Implemented proof

The proof applies the published theorem
`Langlands.AbelianScheme.smoothFamilyPicardZeroComparison_of_inputs` from
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonReduction`.
It discharges that theorem's four arguments with these published theorems,
in order:

1. `Langlands.AlgebraicGeometry.Picard.fieldCubeTrivialitySmoothThird`,
   imported from `Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityProof`.
   This is the cube theorem with a smooth, geometrically connected third
   factor, which need not be proper.
2. `Langlands.AbelianScheme.smoothGeometricIntegrality`, imported from
   `Langlands.AbelianScheme.SmoothGeometricIntegralityProof`.
   A smooth geometrically connected scheme over a field is geometrically
   integral.
3. `Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence`, imported
   from `Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof`.
   This supplies an actual ample line bundle on every commutative smooth
   proper geometrically connected group scheme over an algebraically closed
   field.
4. `Langlands.AbelianScheme.algClosedFieldTranslationDifferenceLifting`,
   imported from
   `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof`.
   With an actual ample bundle and an actual tensor inverse, it expresses a
   translation-invariant bundle as a translation difference. Its
   tensor-preservation argument is supplied inside the published reduction
   by `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`.

The reduction assembles both directions of the field equivalence. In the
forward direction, its imported proof applies the cube theorem to the actual
smooth-family witness and uses the two endpoint restriction isomorphisms to
obtain invariance under every translation. In the reverse direction, it
obtains an ample bundle `H` and an actual tensor inverse `N`, then the lifting
theorem supplies a section `x` and an isomorphism from `t_x^*H ⊗ N` to `L`.
It uses `A` itself as the parameter and the actual bundle
`μ^*H ⊗ pr₂^*N` on the parameter-first product `A ×_K A`.
Geometric integrality follows from the second input. The endpoints are the
identity and `x`, with the implemented restriction isomorphisms to the
trivial bundle and `L`.

The reduction then invokes
`Langlands.AbelianScheme.smoothFamilyPicardZeroComparison_of_field`.
That theorem keeps the field equivalence as the first conjunct and derives
the other three. It applies the equivalence pointwise to each actual
`fibreLineBundle`. The family comparison specializes this to the same
`familyLineBundle`, whose definition uses the inverse of
`relativeSpaceSymmetry`. Quotient induction on actual representatives gives
the rigidified-class comparison.

## Provenance and scope

This is a derived composition of the named published Lean theorems. It
introduces no independent literature assertion or new geometric construction.
The companions of the reduction and its inputs document their mathematics
and original sources. The field equivalence and all three lifts are proved
here by supplying unconditional proofs of every input to that reduction.

The theorem uses the unchanged published smooth-family and translation
predicates, including the actual parameter, rational points, family and
endpoint isomorphisms. It adds no comparison, projectivity, representability,
dual-existence, quasi-separatedness or reducedness hypothesis. The target,
its imported closure, and the parent relative dual-existence statement and
its imported closure are unchanged. The conclusion is exactly the aggregate
comparison; the separate relative dual-existence and openness tasks retain
their own proof obligations.

Worker 2232 wrote this assembly and explanation. The imported results retain
the authorship recorded in their companions.
