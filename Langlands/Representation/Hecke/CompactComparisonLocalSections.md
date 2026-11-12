# Local sections in the elementary comparison range

`compactSectionTest H μH K hK` is the ambient test function
`μH(H ∩ K)⁻¹ 1_K`, where `H` is a subgroup of a locally compact Hausdorff
nonarchimedean group `G`, `μH` is a left Haar measure on `H`, and `K` is a
compact open subgroup of `G`. The actual coefficient subgroup is the published
`Induction.conjOpenSubgroup H K 1`; its members are exactly the `h : H`
whose ambient value lies in `K`. Thus this test is normalized by the subgroup
measure, independently of any ambient Haar measure.

For closed `H` and a smooth complex representation `ρ` on an algebraic vector
space `V`, `compactComparisonFunction_sectionTest` proves the equality

```text
compactComparisonFunction (μH(H ∩ K)⁻¹ 1_K) w
  = compactDoubleCosetSection H (twist relativeModularCharacter ρ) K 1 w,
```

provided `w` is fixed by `H ∩ K` in the twisted representation. This is an
equality in the original `Induction.CompactFunctions`, not an equality in a
new model. `compactComparisonFunction_leftTranslate` identifies left
translation of the input test by `g` with right translation of the output
by the original compact-induced representation.

`compactComparison_span` proves that elementary comparison outputs span the
whole original compact induction. The last theorem,
`compactComparison_surjective_of_pure_values`, therefore states: if an additive
map from any additive commutative group into this compact induction has every
elementary comparison output in its range, that map is surjective. The premise
only specifies the range on elementary comparison values; it does not assume
surjectivity, an inverse, or a complex module structure on the source.

The Lean proof proceeds as follows.

- `compact_identityCoefficientSubgroup` uses closedness of `H` and the
  compactness of `K` to show that the actual intersection subgroup is compact.
  `relativeModularCharacter_identityCoefficient` then proves that both
  modular factors are one on this subgroup.
- `compactSectionTest_apply` and `compactSectionTest_biInvariant` record
  pointwise evaluation and left/right `K` invariance.
  `compactSubgroupTest_sectionTest` identifies the comparison subgroup
  test at `1` with the normalized indicator of `H ∩ K`.
- `compactComparisonValue_sectionTest_one` applies the published
  fixed-vector averaging identity. The relative twist is trivial on the
  compact subgroup, so the twisted fixed vector is also fixed for `ρ`.
- To prove `compactComparisonFunction_sectionTest`, covariance and right
  `K` invariance determine values on `H K` from the value at `1`. Off
  `H K`, the subgroup test is identically zero; the original double-coset
  section also vanishes, by its quotient-support bound.
- Left translation is checked directly on the defining subgroup tests.
  The published `compactLocalSectionSpanning` supplies the spanning
  generators, and the preceding identities place each in the elementary
  comparison range.
- The final additive surjectivity statement uses span induction with the
  strengthened predicate that every complex multiple lies in the additive
  range. On a generator, bilinearity moves that scalar to its input test.
  Additivity handles sums; multiplication of scalars handles the scalar
  induction case.

This is derived infrastructure for Renard III.2.6, proof on printed pp.76–77 /
PDF pp.82–83, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It uses the exact `CompactInductionComparison` construction and the published
compact-local-section and averaging results. The domain and carrier universes
are independent. No finiteness of `H \ G / K`, second countability,
unimodularity, or topology on `V` is assumed. Injectivity and descent through
the Hecke tensor relations remain separate obligations.
