# A geometric Borel subgroup stays Borel over the separable closure

This internal module supports the proof of `StarActionQuasiSplitStatement`
([`StarActionQuasiSplitProof`](StarActionQuasiSplitProof.md)). Its provenance is internal:
it combines the published field-extension lemmas for Borel subgroups with fpqc reflection
of isomorphisms.

## Declarations (namespace `Langlands.GroupScheme.StarActionQuasiSplit`)

- `separableClosure_comp_eq`: the base change morphism `Spec k̄ → Spec k`
  (`toAlgebraicClosure k`, with `k̄ = AlgebraicClosure k`) is the composite of
  `Spec k̄ → Spec k_s` and `Spec k_s → Spec k` (`algebraBaseMap k (SeparableClosure k)`).
  This is the scalar tower `k → k_s → k̄` (Mathlib's `IsScalarTower.algebraMap_eq`).
- `isBorelSubgroup_separableClosure`. Hypotheses: `G` over `Spec k` with affine structure
  map, and `b : B ⟶ G` with `IsGeometricBorelSubgroup b` (a Borel subgroup over `k` whose
  base change to `k̄` is a Borel subgroup). Conclusion: the base change of `b` to
  `k_s = SeparableClosure k` is a Borel subgroup (`IsBorelSubgroup`).

## Proof

The published `BorelFieldExtension.isBorelSubgroup_baseChange_of_maximal`
(`Absolute/BorelFieldExtensionFields`) supplies every field of `IsBorelSubgroup` except
maximality. For maximality, let `f : B_{k_s} ⟶ B'` and a closed subgroup `i' : B' ⟶ G_{k_s}`
with `B'` smooth, connected and solvable satisfy `f ≫ i' = b_{k_s}`; `B'` has affine
structure map by `BorelFieldExtension.isAffineHom_source` (`Absolute/BorelFieldExtensionFields`).
Base change along `c : Spec k̄ → Spec k_s`, which is surjective, flat and quasi-compact by
`fieldExtension_fpqc` (`BaseChangeReflection`). The published comparison isomorphisms
`Descent.pullbackComparison` (`Descent/Data`) identify the iterated base changes of `B` and
`G` with their base changes to `k̄`, and `Descent.pullbackComparison_naturality`
(`Descent/Data`) makes the composite `B_{k̄} → B'_{k̄} → G_{k̄}` equal to `b_{k̄}`. The group
`B'_{k̄}` is a closed subgroup (`IsClosedSubgroup.baseChange`, `SubgroupBaseChange`;
`IsClosedSubgroup.comp_iso`, `Rational/SplitRankTransport`), smooth, connected
(`connectedSpace_baseChange_of_smooth_affine`, `GeometricConnectedness`) and solvable
(`solvableFieldExtensionStatement`, `Absolute/SolvableFieldExtensionProof`). Maximality of
the Borel subgroup `b_{k̄}` makes the map `B_{k̄} → B'_{k̄}` an isomorphism; hence `f_{k̄}` is
an isomorphism, and the published `isIso_of_baseChange` (`BaseChangeReflection`) shows that
`f` is an isomorphism.
