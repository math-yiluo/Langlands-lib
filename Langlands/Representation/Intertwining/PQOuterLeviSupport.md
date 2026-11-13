# Support of `P₁P₂` inside `Q₁Q₂`

Lean module: `Langlands.Representation.Intertwining.PQOuterLeviSupport`.

This module proves the support step of Renard VII.3.5 (iii) (Renard 2026, French version of
9 July 2026, printed pp.239–240 / PDF pp.245–246): the boundary of the open double coset
`P₁(F)P₂(F)` lies in the boundary of `Q₁(F)Q₂(F)`, so that the stage identification
`i_{P₁}^G(σ) ≃ i_{Q₁}^G(i_{P'}^L(σ))` maps `F̃^{<1̄}_{P₁P₂}(σ)` onto a space containing
`F̃^{<1̄}_{Q₁Q₂}(i_{P'}^L(σ))`. Renard uses this tacitly; the proofs are internal.

## Declarations

### Abstract closure lemma

- `doubleCoset_mem_of_mem_closure`: let `H` be a topological group, `P₁, P₂, Q₂` subgroups
  with `P₂` closed, `P₂ ≤ Q₂`, `P₁ ∩ Q₂ ≤ P₂`, and suppose the orbit map
  `Q₂ → P₁\P₁Q₂`, `b ↦ P₁ b` (`Geometric.cosetOrbitMap P₁ Q₂ 1`) is open onto the orbit with
  its subspace topology. If `g ∈ closure (P₁P₂)` and `g ∈ P₁Q₂`, then `g ∈ P₁P₂`.

  Proof: write `g = p b` with `p ∈ P₁`, `b ∈ Q₂`, and suppose `b ∉ P₂`. The set
  `Ω = Q₂ \ P₂` is open in `Q₂`, so its image under the orbit map is open in the orbit: it is
  `Wq ∩ orbit` for an open `Wq ⊂ P₁\H`. Its preimage `W` in `H` is an open neighbourhood of
  `g`, so it meets `P₁P₂` in some `h = p' b'` with `b' ∈ P₂`. Then `P₁ b' = P₁ c` for some
  `c ∈ Ω`, so `b' c⁻¹ ∈ P₁ ∩ Q₂ ⊂ P₂`, whence `c ∈ P₂`, contradicting `c ∈ Ω`.

### Nested parabolics

For nested represented parabolics `P = MN ⊂ Q = LU` with a represented parabolic
`P_L = MN_L` of `L` with the same embedded `M` and `P_L(F) = L(F) ∩ P(F)`, both following from
`nestedParabolicPointDecomposition`:

- `pointImage_radical_le_of_nested`: `U(F) ⊂ N(F)` (from `N(F) = (L(F) ∩ N(F)) U(F)`).
- `exists_mul_of_mem_of_nested`: every `x ∈ P(F)` is `y v` with `y ∈ P_L(F)`, `v ∈ U(F)`
  (from `P(F) = P_L(F) U(F)`).

### Two parabolics with the same Levi

- `radical_inf_parabolic_le_radical`: for represented parabolics `Q₁ = LU₁`, `Q₂ = LU₂` with
  the same embedded Levi, `U₁(F) ∩ Q₂(F) ⊂ U₂(F)`. Proof: choose cocharacters `ξ`, `ψ` with
  `Q₁ = P(ξ)`, `Q₂ = P(ψ)`, `L = Z(ξ) = Z(ψ)`; then `U₁ = U(ξ)`, `U₂ = U(ψ)` and
  `U(ξ) ∩ P(ψ) = U(ξ) ∩ U(ψ)` (`Dynamic.unipotent_inf_parabolic_eq_unipotent_inf_unipotent`).

### Open orbit map

- `isOpenMap_parabolic_cosetOrbitMap`: for represented parabolics `P` (with a rational Levi)
  and `Q` (with a rational Levi) of a connected reductive `G` over a nonarchimedean local
  field, with `G(F)` locally compact and nonarchimedean, the orbit map
  `Q(F) → P(F)\P(F)Q(F)` is open. Proof: `G(F)` is Hausdorff and second countable, hence
  σ-compact; `P(F)\G(F)/Q(F)` is finite (`representedParabolicDoubleCoset`), so the closed
  subgroup orbit ordering (`Geometric.closedSubgroupOrbitOrdering`) yields a Bruhat-refining
  linear order, whose boundary-vanishing support pair at `1`
  (`Geometric.boundaryVanishingSupportPair`) shows that the orbit of `1` is locally closed;
  `Geometric.isOpenMap_cosetOrbitMap` concludes.

### The outer Levi configuration

The section `Outer` takes the data and hypotheses of `PQIntertwiningOuterLeviStatement`
(without the opposites): `P₁ = MN₁ ⊂ Q₁ = LU₁`, `P₂ = MN₂ ⊂ Q₂ = LU₂`, `l₂ ≫ p₂ = l₁ ≫ p₁`,
`lQ₂ ≫ q₂ = lQ₁ ≫ q₁`, and `P' = MN'` in `L` with
`P'(F) = P₁(F) ∩ L(F) = P₂(F) ∩ L(F)`.

- `outer_radical₁_le`: `U₁(F) ⊂ N₁(F)`; `outer_radical₂_le`: `U₂(F) ⊂ N₂(F)` (nested case).
- `outer_parabolic_inf_le`: `P₁(F) ∩ Q₂(F) ⊂ P₂(F)`. Write `c ∈ P₁ ∩ Q₂` as `y v` with
  `y ∈ P'`, `v ∈ U₁`; `y ∈ P' ⊂ P₂ ⊂ Q₂`, so `v ∈ U₁ ∩ Q₂ ⊂ U₂ ⊂ N₂`, and `c ∈ P₂`.
- `outer_doubleCoset_mk_eq_one`: `Q₁(F)Q₂(F) ⊂ P₁(F)Q₂(F)`, on double-coset classes of `g`.
  Write `g = a b` with `a ∈ Q₁`, `b ∈ Q₂`, and `a = (a y⁻¹) y` with `y` the Levi projection of
  `a` in `L(F)`; then `a y⁻¹ ∈ U₁ ⊂ N₁ ⊂ P₁` and `y b ∈ Q₂`.
- `outer_boundary_subset`: `closure (P₁P₂) \ P₁P₂ ⊂ closure (Q₁Q₂) \ Q₁Q₂` (with `G(F)`
  carrying its canonical topology, locally compact and nonarchimedean). The closure part
  follows from `P₁P₂ ⊂ Q₁Q₂`. If `g ∈ closure (P₁P₂)` lay in `Q₁Q₂`, then `g ∈ P₁Q₂` by
  `outer_doubleCoset_mk_eq_one`, and `doubleCoset_mem_of_mem_closure` (with
  `outer_parabolic_inf_le` and the open orbit map of `Q₂(F)` on `P₁(F)\G(F)`) gives
  `g ∈ P₁P₂`.
