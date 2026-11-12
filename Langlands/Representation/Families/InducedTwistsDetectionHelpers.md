# Auxiliary facts for the uniform induced-twist detector

Author: Worker 70. Module
`Langlands.Representation.Families.InducedTwistsDetectionHelpers`, namespace
`Langlands.Renard.AlgebraicFamily.InducedTwistsDetection`.

## Statements and proofs

- `le_normalizer_of_subgroupOf_normal`: if `K ≤ K₀` and `K` is normal in `K₀`
  (`(K.subgroupOf K₀).Normal`), then `K₀ ≤ normalizer K`. This is a direct group-theoretic
  computation. It converts the normality clause of the published `CompactOpenNormalBasis`
  into the normalizer hypothesis of the VI.9.4 Corollary statement.
- `exists_standard_minimal_factorization`: let `T → G` be a maximal split torus, `ν` a
  generic cocharacter and `K₀` a subgroup satisfying the published product equalities
  `BruhatTits.Iwasawa.StandardParabolicProducts i ν K₀`. Then every `g ∈ G(k)` is
  `m * n * c` with `m ∈ standardLeviPoints i ν ∅`, `n ∈ standardUnipotentPoints i ν ∅` and
  `c ∈ K₀`. Proof: the product equality for `J = ∅` gives `g = x * c` with
  `x ∈ P_∅(k)`. The proved `standardCocharacter` identifies `P_∅`, `M_∅` and `U_∅` with
  the dynamic subgroups of a standard cocharacter. The semidirect decomposition
  `dynamic_isSemidirectDecomposition` then splits `x` into its Levi projection and a
  radical factor.
- `leviInduction_generate_of_universeLift`: for a smooth `τ` of `M(k)` with carrier in
  `Type v` and any subgroup `K` of `G(k)`, generation of
  `leviInductionFunctor.{u, max u v}` applied to the universe lift
  `SmoothRep.universeLift.{u} τ` by its `K`-fixed vectors implies generation of
  `leviInductionFunctor.{u, v}` applied to `τ` by its `K`-fixed vectors. Proof: the
  representation equivalence `τ ≃ universeLift τ` induces an equivalence of the two
  normalized inductions (`normalizedInductionEquivOfEquiv`). Generation transfers along
  equivalences (`NormalizedJacquetBridge.generation_of_equiv`).
