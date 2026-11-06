# Double-coset operators on fixed vectors for compact open levels

This internal construction defines, for a representation of a topological
group `G` over an arbitrary commutative ring `R`, the double-coset operator
`[K g L] : V^L → V^K` between the vectors fixed by two compact open levels
`K` and `L`:

`[K g L] v = ∑_{k ∈ K / (K ∩ g L g⁻¹)} ρ(k g) v`.

It proves that the sum is well defined and `K`-fixed, that the operator is
`R`-linear, depends only on the double coset `K g L`, is the inclusion
`V^L ⊆ V^K` when `g = 1` and `K ⊆ L`, and commutes with intertwining maps.
It packages the operators as natural transformations between fixed-vector
functors on smooth representations, and evaluates them on classes of a fixed
level in the published colimits over levels. All declarations are in
namespace `Langlands.Shimura.LevelHecke`.

## Motivation and scope

The Harris framework needs Hecke operators at finite level on cohomology with
coefficients in rings such as `ℤ/ℓ^n` or `ℤ_ℓ`, where no Haar-measure
normalization is available. The published complex construction
`Langlands.Representation.Hecke.DoubleCoset` integrates against a Haar measure
with complex coefficients; the published
`Langlands.Shimura.EquivariantFormsHecke` treats spaces of forms. This module
gives the unnormalized coset-sum operator for an arbitrary representation and
ring. The cosets `k g L`, for `k` running over `K / (K ∩ g L g⁻¹)`, are the left
`L`-cosets contained in `K g L`; this standard description explains the
formula but is not formalized here.

The module does not construct the Hecke algebra, its multiplication or the
composition law of two double-coset operators. It makes no comparison with
the Haar-measure operators of `Hecke.DoubleCoset`, and no geometric Hecke
correspondence on the schemes of a tower. Identifying the `K`-fixed vectors of
colimit cohomology with the cohomology at level `K` is a separate theorem
obligation.

## The cosets

Let `G : Type v` be a topological group. The published
`CompactOpenLevel.heckeLevel K L g` is the compact open level `K ∩ g L g⁻¹`.

- `mem_heckeLevel` states
  `x ∈ heckeLevel K L g ↔ x ∈ K ∧ g⁻¹ * x * g ∈ L`.
- `HeckeCosets K L g` is the quotient
  `K.subgroup ⧸ (heckeLevel K L g).subgroup.subgroupOf K.subgroup` of left
  cosets in `K`.
- The instance `finite_heckeCosets` proves that it is finite: `K` is a compact
  space, and `K ∩ g L g⁻¹` is an open subgroup of it, so Mathlib's
  `Subgroup.quotient_finite_of_isOpen` applies. `fintype_heckeCosets` is the
  resulting `Fintype` instance, used for the sums.

## The operator

Let `R : Type t` be a commutative ring and `ρ : Representation R G V` on an
`R`-module `V : Type w`. The published `fixedVectors ρ H` is the submodule of
vectors fixed by a subgroup `H`.

- `map_mul_mem_heckeLevel` states that, for `v` fixed by `L` and
  `m ∈ K ∩ g L g⁻¹`, `ρ(k m g) v = ρ(k g) v`, because
  `k m g = (k g)(g⁻¹ m g)` with `g⁻¹ m g ∈ L`.
- `cosetTerm ρ K L g v q` is `ρ(k g) v` for any representative `k` of the
  coset `q`; it is well defined by the previous lemma (`cosetTerm_mk`,
  `cosetTerm_eq_out`). It is additive and `R`-linear in `v`
  (`cosetTerm_add`, `cosetTerm_smul`).
- `map_cosetTerm` states `ρ(k) (cosetTerm v q) = cosetTerm v (k • q)` for
  `k ∈ K`. Hence `sum_cosetTerm_mem`: the sum over all cosets is fixed by `K`,
  since left multiplication by `k` permutes the cosets.
- `heckeOperator ρ K L g : fixedVectors ρ L →ₗ[R] fixedVectors ρ K` sends `v`
  to this sum (`heckeOperator_apply`), and `heckeOperator_apply_out` expresses
  it with Mathlib's chosen representatives `q.out`.
- `heckeOperator_one_of_le` states that, if `K ⊆ L`, then `[K 1 L] v = v`:
  there is a single coset. `heckeOperator_self` states `[K 1 K] = id`.
- `heckeOperator_mul_right` states `[K (g l) L] = [K g L]` for `l ∈ L`: the
  levels `K ∩ (g l) L (g l)⁻¹` and `K ∩ g L g⁻¹` coincide, and
  `ρ(k g l) v = ρ(k g) v`. `heckeOperator_mul_left` states
  `[K (k g) L] = [K g L]` for `k ∈ K`: right multiplication by `k` identifies
  the cosets of `K ∩ (k g) L (k g)⁻¹` with those of `K ∩ g L g⁻¹`, matching
  the terms. `heckeOperator_mul_mul` combines them: the operator depends only
  on the double coset `K g L`.
- `fixedVectorsMap_heckeOperator` states that the operator commutes with the
  published restriction `fixedVectorsMap f` of an intertwining map `f` to
  fixed vectors.

## Smooth representations

- `fixedVectorsFunctor R H : SmoothRep R G ⥤ ModuleCat R` sends a smooth
  representation to its `H`-fixed vectors and a morphism to
  `fixedVectorsMap` of its intertwining map (`fixedVectorsFunctor_obj`). It
  needs no topology on `G` beyond that of `SmoothRep`.
- `heckeNatTrans R K L g` is the natural transformation from the `L`-fixed
  to the `K`-fixed vector functor with components `heckeOperator`
  (`heckeNatTrans_app`); naturality is `fixedVectorsMap_heckeOperator`.
  `heckeNatTrans_self` states that `[K 1 K]` is the identity.

## Classes of a fixed level in colimits over levels

Let `F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat R` be level-trivial in the sense
of the published `LevelColimit.IsLevelTrivial`, with the colimits over the
published ordered levels, and let `LevelColimit.smoothRep F hF` be its
published smooth colimit representation.

- `ι_apply_mem_fixedVectors` states that the image `(LevelColimit.ι F K).hom x`
  of a class of level `K` is fixed by `K`, by the published
  `translate_ι_apply_of_mem`.
- `levelClass F hF K` is the resulting linear map from `F(K)` to the
  `K`-fixed vectors of the colimit (`levelClass_apply_coe`).
- `heckeOperator_levelClass` states that `[K g L]` sends the image of a class
  `x` of level `L` to
  `∑_q ι_{(k_q g) L (k_q g)⁻¹} (F(conjArrow (k_q g) L) x)`, where `k_q` is the
  chosen representative of `q`, by the published `smoothRep_ρ_ι_apply`.
  Applied to the published colimit cohomology of level towers, this is the
  double-coset operator on classes of level `L`.

## Provenance

This is an internal construction from Mathlib's subgroup quotients,
`QuotientGroup.induction_on`, `Quotient.congr`, `Subgroup.quotientEquivOfEq`,
`Fintype.sum_equiv`, `Subgroup.quotient_finite_of_isOpen` and
`Representation.IntertwiningMap`, together with the published
`CompactOpenLevel.heckeLevel`, `fixedVectors`, `fixedVectorsMap`,
`SmoothRep` and the `LevelColimit` constructions. No operator, invariance or
compatibility is supplied as input.
