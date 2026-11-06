# Translation and composition laws of double-coset operators

This internal construction extends the double-coset operators
`[K g L] : V^L → V^K` of `Langlands.Shimura.LevelHecke`, for a representation
`ρ : Representation R G V` of a topological group over an arbitrary
commutative ring `R`. It counts the cosets in the defining sum, defines the
translation `ρ(h) : V^L → V^{h L h⁻¹}`, proves how the operators interact with
translations and conjugation, and proves the composition laws of the
inclusions `[K 1 L]` (for `K ⊆ L`) and traces `[L 1 K]` (for `K ⊆ L`),
including `[L 1 K] ∘ [K 1 L] = [L : K]`. The composition laws are also stated
for the natural transformations of fixed-vector functors on smooth
representations, and the translation is evaluated on classes of a fixed level
in the published colimits over levels. All declarations are in namespace
`Langlands.Shimura.LevelHecke`.

## Motivation and scope

Hecke operators at varying level on the cohomology of the Harris level
towers, with coefficients such as `ℤ/ℓ^n`, are built from the translations
`ρ(h)` and from inclusions and traces between levels. This module records the
laws relating these pieces that hold without dividing by indices.

The module does not construct the Hecke algebra or its multiplication, and it
proves no composition law of two general double-coset operators
`[K g L] ∘ [L h M]` beyond the cases above, where one factor is an inclusion
or a trace. No Haar measure or normalization is used, and no comparison with
the Haar-measure operators of `Langlands.Representation.Hecke.DoubleCoset` is
made. Geometric Hecke correspondences on the schemes of a tower, and the
identification of `K`-fixed vectors of colimit cohomology with cohomology at
level `K`, are separate obligations.

## Numbers of cosets

Let `G : Type v` be a topological group and `K L : CompactOpenLevel G`.

- `heckeLevel_subgroup_eq` states that the subgroup of the published
  `heckeLevel K L g` is `K ⊓ g L g⁻¹`, written with the published
  `conjLevel g L`.
- `card_heckeCosets` states that the number of elements of
  `HeckeCosets K L g = K / (K ∩ g L g⁻¹)` is the Mathlib relative index
  `(conjLevel g L).subgroup.relIndex K.subgroup`, that is, the index of
  `g L g⁻¹ ∩ K` in `K`. `card_heckeCosets_one` is the case `g = 1`: the
  number of cosets `K / (K ∩ L)` is `L.subgroup.relIndex K.subgroup`.

## Translation by group elements

Let `R : Type t` be a commutative ring, `V : Type w` an `R`-module and
`ρ : Representation R G V`; the representation need not be smooth.

- `translateFixed ρ h L : fixedVectors ρ L →ₗ[R] fixedVectors ρ (h L h⁻¹)`
  sends `v` to `ρ(h) v` (`translateFixed_apply_coe`). The image is fixed by
  `h L h⁻¹`, since `x h = h (h⁻¹ x h)` with `h⁻¹ x h ∈ L`.
- `heckeOperator_comp_translateFixed` states
  `[K x (h L h⁻¹)] ∘ ρ(h) = [K (x h) L]`. The levels
  `K ∩ x (h L h⁻¹) x⁻¹` and `K ∩ (x h) L (x h)⁻¹` coincide, and
  `ρ(k x) ρ(h) v = ρ(k x h) v`.
- `heckeOperator_eq_comp_translateFixed` is the case `x = 1`:
  `[K g L] = [K 1 (g L g⁻¹)] ∘ ρ(g)`, so every double-coset operator is a
  translation followed by the operator of the coset `K 1 (g L g⁻¹)`.
- `translateFixed_comp_heckeOperator` states
  `ρ(h) ∘ [K g L] = [(h K h⁻¹) (h g) L]`. Conjugation `k ↦ h k h⁻¹`
  identifies `K / (K ∩ g L g⁻¹)` with
  `h K h⁻¹ / (h K h⁻¹ ∩ (h g) L (h g)⁻¹)`, and the terms match because
  `h k h⁻¹ h g = h k g`.
- `translateFixed_comp_heckeOperator_conj` combines the two:
  `ρ(h) ∘ [K g L] = [(h K h⁻¹) (h g h⁻¹) (h L h⁻¹)] ∘ ρ(h)`.

## Inclusions and traces

Let `K L M : CompactOpenLevel G`. When `K ⊆ L`, the published
`heckeOperator_one_of_le` identifies `[K 1 L] : V^L → V^K` with the inclusion,
and `[L 1 K] : V^K → V^L` is the trace `v ↦ ∑_{q ∈ L / K} ρ(l_q) v`.

- `heckeOperator_comp_of_le_of_le` states that for `M ⊆ K ⊆ L` the inclusions
  compose: `[M 1 K] ∘ [K 1 L] = [M 1 L]`.
- `heckeOperator_trace_comp_inclusion` states that for `K ⊆ L`,
  `[L 1 K] ∘ [K 1 L]` is multiplication by `K.subgroup.relIndex L.subgroup`,
  the index of `K` in `L`: each of the `[L : K]` terms `ρ(l_q) v` equals `v`
  for `v` fixed by `L`, and the count is `card_heckeCosets_one`.
- `heckeOperator_comp_of_ge_of_ge` states that for `M ⊆ K ⊆ L` the traces
  compose: `[L 1 K] ∘ [K 1 M] = [L 1 M]`. The proof identifies `L / M` with
  pairs in `L / K × K / M` by Mathlib's `Subgroup.quotientEquivProdOfLE`
  (which uses chosen representatives of `L / K`) followed by the
  identification of `(L ∩ K) / (L ∩ M)` with `K / M` through `Quotient.congr`,
  and matches `ρ(l_a) ρ(k_b) v = ρ(l_a k_b) v` term by term.
- `heckeOperator_trace_comp_of_conjLevel_le` states that if
  `g M g⁻¹ ⊆ K ⊆ L` then `[L 1 K] ∘ [K g M] = [L g M]`, and
  `heckeOperator_comp_trace_of_conjLevel_le` states that if `M ⊆ L` and
  `g L g⁻¹ ⊆ K` then `[K g L] ∘ [L 1 M] = [K g M]`. Both follow from the
  factorization through `ρ(g)` above and the transitivity of traces; the
  second also uses `translateFixed_comp_heckeOperator` to move `ρ(g)` past
  `[L 1 M]`, giving `[(g L g⁻¹) g M]`.

## Natural transformations

For the published `heckeNatTrans R K L g` from the `L`-fixed to the `K`-fixed
vector functor on `SmoothRep R G`:

- `heckeNatTrans_comp_of_le_of_le`: for `M ⊆ K ⊆ L`,
  `heckeNatTrans R K L 1 ≫ heckeNatTrans R M K 1 = heckeNatTrans R M L 1`.
- `heckeNatTrans_comp_of_ge_of_ge`: for `M ⊆ K ⊆ L`,
  `heckeNatTrans R K M 1 ≫ heckeNatTrans R L K 1 = heckeNatTrans R L M 1`.

Both are proved componentwise from the corresponding operator laws.

## Classes of a fixed level in colimits over levels

Let `F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat R` be level-trivial in the sense
of the published `LevelColimit.IsLevelTrivial`, with colimits over the
published ordered levels, and let `levelClass F hF L` be the map from `F(L)` to
the `L`-fixed vectors of the published `LevelColimit.smoothRep F hF`.

- `translateFixed_levelClass` states that translating the image of a class
  `x` of level `L` by `h` gives the image at level `h L h⁻¹` of
  `F(conjArrow h L) x`, by the published `smoothRep_ρ_ι_apply`.

## Provenance

This is an internal construction from Mathlib's `Subgroup.relIndex`,
`Subgroup.inf_relIndex_left`, `Subgroup.quotientEquivOfEq`,
`Subgroup.quotientEquivProdOfLE`, `Quotient.congr`, `Fintype.sum_equiv`,
`Fintype.sum_prod_type` and `QuotientGroup.induction_on`, together with the
operators, cosets, fixed-vector functors and level classes of
`Langlands.Shimura.LevelHecke` and the published `conjLevel`, `conjArrow`,
`fixedVectors` and `LevelColimit.smoothRep_ρ_ι_apply`. No operator, identity
or composition law is supplied as input. The laws are the standard properties
of double-coset operators, proved here for the unnormalized coset sums.
