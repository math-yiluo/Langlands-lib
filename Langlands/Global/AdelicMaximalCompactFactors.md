# Maximal compact subgroups of `G(𝔸_F)` and their infinite and finite factors

Let `F` be a number field and `G` an affine group scheme over `Spec F`. The
published multiplicative homeomorphism `AdelicGroupPoints.split` identifies the
actual adelic point group `G(𝔸_F)` with the product
`G(𝔸_{F,∞}) × G(𝔸_{F,f})` of the actual infinite and finite point groups. This
module shows that a maximal compact subgroup `K` of `G(𝔸_F)` is the product
`K_∞ × K_f` of two maximal compact subgroups, one in each factor, and
conversely. It also shows that a compact subgroup serving a smaller group
`P₀ → P` in the published parabolic Iwasawa predicate serves `P`.

"Maximal compact" means the published predicates
`CompactIwasawa.IsMaximalCompact` (a compact subgroup contained in no strictly
larger compact subgroup) and `AdelicGroupPoints.IsMaximalCompactSubgroup`
(the same condition on `G(𝔸_F)`). The factors are
`K_∞ = K.comap ofInfinite = {x : (x, 1) ∈ K}` and
`K_f = K.comap ofFinite = {y : (1, y) ∈ K}`, where `ofInfinite` and `ofFinite`
are the published inclusions of the two factors.

## Provenance

The content is internal. It is the elementary topology of products of
topological groups, specialized through the published product decomposition
`AdelicGroupPoints.split` (module `Langlands.Global.AdelicGroupProduct`).
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*, I.1.1
(printed p. 1), fix a maximal compact subgroup `K = ∏_v K_v` of `G(𝔸)` with
each `K_v` maximal compact in `G(k_v)`. This module proves only the coarser
infinite/finite splitting, and proves it for an arbitrary maximal compact `K`
rather than assuming it. Worker 3657
requested it: they need `K_∞` maximal compact in `G(𝔸_{F,∞})` for the
archimedean side of the Eisenstein-series and growth constructions.

## Declarations

Generic products, in namespace `Langlands.CompactIwasawa`, for topological
groups `A` and `B`:

- `isCompact_subgroupProd`: `H × L` is compact when `H` and `L` are. Proof:
  `IsCompact.prod`.
- `le_prod_map_fst_map_snd`: every subgroup `K ≤ A × B` lies in the product of
  its two projections. Proof: unfold membership.
- `isCompact_map_fst`, `isCompact_map_snd`: the projections of a compact
  subgroup are compact. Proof: continuous images of compact sets.
- `IsMaximalCompact.eq_prod_map`: a maximal compact `K` equals the product of
  its projections. Proof: the product of the projections is compact and
  contains `K`, so maximality gives equality.
- `IsMaximalCompact.comap_inl_eq_map_fst`, `IsMaximalCompact.comap_inr_eq_map_snd`:
  for maximal compact `K`, the points `(a, 1)` of `K` are exactly the first
  projection, and the points `(1, b)` exactly the second. Proof: rewrite `K`
  as the product of its projections.
- `IsMaximalCompact.comap_inl`, `IsMaximalCompact.comap_inr`: each factor of a
  maximal compact `K` is maximal compact. Proof: if a compact `L` contains the
  first projection, then `L × (second projection)` is compact and contains
  `K`, so it equals `K` by maximality. Hence `L` lies in the first projection.
  The second factor is symmetric.
- `IsMaximalCompact.prod`: the product of two maximal compact subgroups is
  maximal compact. Proof: a compact `M ⊇ H × L` has compact projections
  containing `H` and `L`, which are therefore `H` and `L`. So `M ≤ H × L`.
- `isMaximalCompact_prod_iff`: `H × L` is maximal compact exactly when `H` and
  `L` are. Proof: the previous two items; the factors of `H × L` are `H` and
  `L`.
- `isMaximalCompact_comap_equiv`: maximality is preserved under pullback along
  a topological group isomorphism. Proof: the published
  `IsMaximalCompact.map` applied to the isomorphism and its inverse.

Adelic points, in namespace `Langlands.Global.AdelicGroupPoints`:

- `isMaximalCompactSubgroup_iff`: `IsMaximalCompactSubgroup F G K` is the
  generic `IsMaximalCompact K`. Proof: `Iff.rfl`.
- `factorSubgroup F G Kinf Kfin`: the subgroup of `g ∈ G(𝔸_F)` with infinite
  part in `Kinf` and finite part in `Kfin`. It is the pullback of
  `Kinf × Kfin` along `split`. `mem_factorSubgroup` states this membership.
- `comap_ofInfinite_factorSubgroup`, `comap_ofFinite_factorSubgroup`: the
  factors of `factorSubgroup F G Kinf Kfin` are `Kinf` and `Kfin`. Proof: the
  projection identities of `ofInfinite` and `ofFinite`.
- `isMaximalCompactSubgroup_factorSubgroup_iff`: `factorSubgroup F G Kinf Kfin`
  is maximal compact exactly when `Kinf` and `Kfin` both are. Proof:
  `isMaximalCompact_comap_equiv` for `split`, then `isMaximalCompact_prod_iff`.
- `comap_ofInfinite_eq`, `comap_ofFinite_eq`: `K.comap ofInfinite` and
  `K.comap ofFinite` are the two factors of the image of `K` under `split`.
  Proof: unfold.
- `IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite` and
  `IsMaximalCompactSubgroup.isMaximalCompact_comap_ofFinite`: for maximal
  compact `K`, `K_∞` is maximal compact in `G(𝔸_{F,∞})` and `K_f` is maximal
  compact in `G(𝔸_{F,f})`. Proof: transport `K` along `split` with the
  published `IsMaximalCompact.map`, then `comap_inl` or `comap_inr`.
- `IsMaximalCompactSubgroup.eq_factorSubgroup`: a maximal compact `K` equals
  `factorSubgroup F G K_∞ K_f`. Proof: `eq_prod_map` for the image of `K`
  under `split`, then pull back along the injective `split`.
- `IsMaximalCompactSubgroup.mem_iff`: for maximal compact `K`, `g ∈ K` exactly
  when `ofInfinite (infinite g) ∈ K` and `ofFinite (finite g) ∈ K`. Proof: the
  previous item.
- `isMaximalCompactSubgroup_iff_exists_factorSubgroup`: `K` is maximal compact
  exactly when `K = factorSubgroup F G Kinf Kfin` for some maximal compact
  `Kinf ≤ G(𝔸_{F,∞})` and `Kfin ≤ G(𝔸_{F,f})`.
- `IsParabolicIwasawaCompact.isMaximalCompact_comap_ofInfinite` and
  `IsParabolicIwasawaCompact.isMaximalCompact_comap_ofFinite`: the same two
  factor statements for a `K` satisfying the published predicate
  `IsParabolicIwasawaCompact F G P p K` (`K` maximal compact and
  `p(P(𝔸_F)) K = G(𝔸_F)`). Proof: its first conjunct.
- `IsParabolicIwasawaCompact.of_comp`: if `K` satisfies the predicate for
  `f ≫ p : P₀ → G`, it satisfies it for `p : P → G`. Proof: the image of
  `P₀(𝔸_F)` lies in the image of `P(𝔸_F)`, because the point map of `f ≫ p`
  is the point map of `f` followed by that of `p`. So
  `G(𝔸_F) = p(f(P₀(𝔸_F))) K ⊆ p(P(𝔸_F)) K`. For example, one `K` with
  `P₀(𝔸_F) K = G(𝔸_F)` for a minimal parabolic `P₀` serves every parabolic
  containing `P₀`.

## Scope

These are structural facts about given subgroups. The module proves no
existence of a maximal compact subgroup, no Iwasawa decomposition, and no
product formula `K_f = ∏_v K_v` over the finite places. The group scheme `G`
needs no reductivity, smoothness or finite-type hypothesis, and `P₀`, `P` and
the homomorphisms `f` and `p` need not be parabolic or injective.
