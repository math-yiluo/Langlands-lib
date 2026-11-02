# Actual dual-valued pullback along morphisms over a base

This internal construction compares the canonical relative base-change
isomorphism with the ordinary composition isomorphism on a literal composite
triangle. Equality follows by comparing the inverses on the two pullback
projections, using the published projection equations.

The namespace is `Langlands.AbelianScheme`. All schemes lie in an arbitrary
universe `u`. For an abelian scheme `B/S`, objects `T,T'` of `Over S` and a
morphism `f : T' ⟶ T`, put

```
BT = (baseChange T.hom).obj B
BD = (baseChange T'.hom).obj B
BC = (baseChange f.left).obj BT
k = relativeBaseChangeComparisonIso B f : BD ≅ BC.
```

`relativeBaseChangeComparisonIso_homMk` identifies `k` with
`baseChangeCompIso b c B` when `T = Over.mk b`,
`T' = Over.mk (c ≫ b)` and `f = Over.homMk c rfl`. The proof compares the
inverse group-object maps on the two pullback projections. The published
Cartier and ordinary composition projection equations give the first
projection equality; both maps are over the same base, giving the second.
Faithfulness of the forgetful maps proves equality of the actual isomorphisms.

Each dual endpoint retains its own `HasDualScheme`, `DualSchemeGeometry`,
inverse Poincare line bundle and evaluation isomorphism. Denote its
`dualAbelianSchemeFromEvaluation` by `D(-)`.
`relativeDualBaseChangeComparisonIso` is the actual isomorphism
`D(BC) ≅ D(BD)` obtained by applying the published
`dualAbelianSchemeIsoFromEvaluation` to `k`. Its forward map is the
contravariant dual of `k.hom`.

Let `lam : B ⟶ D(B)` be any actual dual-valued map. Write `F_T`, `F_D`
and `F_f` for the published `dualAbelianBaseChangeMap` along `T.hom`,
`T'.hom` and `f.left`, with the displayed endpoint data. Then
`dualAbelianBaseChangeMap_relative_comp_pullback` proves

```
(k.hom ≫ F_f(F_T(lam))) ≫ dual(k.hom) = F_D(lam).
```

The proof writes each object and morphism of `Over S` using its underlying
scheme map and commutative triangle, then eliminates the triangle equality.
The preceding comparison lemma identifies `k` with the literal composition
comparison. The published `dualAbelianBaseChangeMap_comp_pullback` supplies
the resulting equation.

The dual isomorphism retains
`pullbackTensorComparisonIsIsoStatement`, `PicardZeroPullbackStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement` and
`PullbackTensorSymmetryStatement`. The map equation additionally retains
`PicardZeroUniversalBaseChangeStatement` and
`DualAbelianBaseChangeStatement`, and the displayed dual data on `B` and
`BT`. None of these input propositions or dual-existence data are proved here.

The provenance is internal compatibility of the existing relative comparison,
ordinary composition comparison and actual dual base-change constructions.
The imports are `RelativeIntegralActionComparison` and
`DualAbelianBaseChangeCoherence`. There is no flatness, reducedness, connectedness
or local noetherianness restriction on a test map. The map need not be a
polarization. This unit identifies actual maps and does not establish
polarized moduli existence, normalized Harris representability, smoothness,
projectivity or admissibility.
