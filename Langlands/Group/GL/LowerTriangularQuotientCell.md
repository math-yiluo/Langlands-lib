# The open lower-triangular cell of `N_m \ GL_m`

Author: Worker 936.

This module proves that the coset map

```text
lowerTriangularQuotientMap m R : lowerTriangularSubgroup m R → LeftQuotient (upperUnipotent m R),
  b ↦ [b] = N_m · b,
```

is injective for every commutative ring, and is an open embedding over a
p-adic field. The image is the open cell `N_m · B̄_m` of the left coset space
`N_m \ GL_m`. All declarations are in the namespace `Langlands.GeneralLinear`.

## Provenance

Internal (derived infrastructure). The module introduces one map, the
restriction of the published quotient map `Quotient.mk _` to the published
subgroup `lowerTriangularSubgroup m R` of invertible lower triangular
matrices, written `B̄_m` in H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983),
section 9.3. Its use is to identify measures on `N_m \ GL_m` with right Haar
measures on `B̄_m`, which is how the source's measure `dg d_r(h) dx` on the
lower-block coordinates is understood. The source states no lemma of this
form; the facts proved here are the standard statements that
`N_m ∩ B̄_m = 1` and that the product set `N_m · B̄_m` is open. They are
proved from Library definitions cited by name below.

## Conventions

`LeftQuotient H` is the published `QuotientIntegration.LeftQuotient H`, the
quotient by `QuotientGroup.rightRel H`, whose points are left cosets `H * k`.
`Quotient.mk _ k = Quotient.mk _ k'` exactly when `k' * k⁻¹ ∈ H`
(`leftQuotient_mk_eq_iff`). `upperUnipotent m R` is the published group of
upper triangular matrices with unit diagonal; `lowerTriangularSubgroup m R` is
the published group of invertible lower triangular matrices. The topology on
`GeneralLinear m F.Carrier` is `T.topology` from a p-adic field's
`F.TopologicalData`, `LeftQuotient` carries the quotient topology, and
`lowerTriangularSubgroup m F.Carrier` carries the subspace topology. No new
topology or instance is installed.

## Definitions

- `lowerTriangularQuotientMap m R b = Quotient.mk _ b.val`
  (simp lemma `lowerTriangularQuotientMap_apply`, by `rfl`), for every
  `m : ℕ` and every commutative ring `R : Type u`.

## Theorems

Algebra (every commutative ring `R`, every `m`):

- `eq_one_of_mem_upperUnipotent_of_mem_lowerTriangular`: an element of
  `GeneralLinear m R` lying in both `upperUnipotent m R` and
  `lowerTriangularSubgroup m R` is `1`. Proof: the Library lemma
  `matrix_eq_one_of_triangular` (upper triangular, lower triangular, unit
  diagonal).
- `singletons_oppositeUnipotentSubgroup_le_lowerTriangular`: the opposite
  unipotent subgroup of the singleton block shape
  `BlockShape.singletons m` lies in `lowerTriangularSubgroup m R`. Proof:
  membership gives membership in the opposite parabolic, whose entries vanish
  between blocks `i < j` (`mem_oppositeParabolic_iff`); with singleton
  blocks, `singletons_index` turns these into the entries `(i, j)`, `i < j`.
- `singletons_leviSubgroup_le_lowerTriangular`: the Levi subgroup of the
  singleton shape lies in `lowerTriangularSubgroup m R`, because Levi
  embeddings vanish between distinct blocks (`leviEmbedding_apply_ne`).
- `lowerTriangularQuotientMap_injective`: if `[b] = [b']` then
  `b' b⁻¹ ∈ upperUnipotent m R ∩ lowerTriangularSubgroup m R = 1`, so
  `b = b'`.

p-adic topology (every prime `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, every `T : F.TopologicalData`, every `m : ℕ`):

- `exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular T m`:
  every neighbourhood `U` of `1` contains a compact open subgroup `K` such that
  each `k ∈ K` is a product `u * c` with `u ∈ upperUnipotent m F.Carrier`,
  `c ∈ lowerTriangularSubgroup m F.Carrier` and `c ∈ K`. Proof: the Library's
  `BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization` for the
  singleton shape gives `K ⊆ U` whose Iwahori product
  `(K ∩ N̄) × (K ∩ M) × (K ∩ N) → K`, `(l, t, v) ↦ l t v`, is bijective.
  Factor `k⁻¹ = l t v`; then `k = v⁻¹ (t⁻¹ l⁻¹)`, where
  `v⁻¹ ∈ upperUnipotent` by `singletons_unipotentSubgroup`, and
  `t⁻¹ l⁻¹ ∈ K` is lower triangular by the two inclusions above.
- `isOpen_upperUnipotent_mul_lowerTriangular_inter T m`: for every open
  `O ⊆ GeneralLinear m F.Carrier`, the set
  `{g | ∃ u ∈ upperUnipotent, ∃ b ∈ lowerTriangularSubgroup, b ∈ O ∧ u * b = g}`
  is open. Proof: at `u * b`, choose `K` as above inside the neighbourhood
  `{c | c * b ∈ O}` of `1`; the neighbourhood `u K b` of `u * b` lies in the
  set, since `u k b = (u u') (c b)` with `k = u' c`.
- `isOpenEmbedding_lowerTriangularQuotientMap T m`: the coset map is an open
  embedding. Continuity: the composite of the subtype inclusion and the
  continuous quotient map. Openness: the image of a relatively open
  `B̄_m ∩ O` is the image under the open quotient map
  (`leftQuotient_isOpenQuotientMap`) of the open set of the previous theorem.
  Mathlib's `IsOpenEmbedding.of_continuous_injective_isOpenMap` concludes.

## Role

The planned disintegration proof for
`Langlands.RankinSelberg.LowerBlockQuotientDisintegrationStatement` (task
7b088130) is to use this open embedding to pull a compatible quotient measure on `N_m \ GL_m` back to a
right Haar measure on `B̄_m`.
