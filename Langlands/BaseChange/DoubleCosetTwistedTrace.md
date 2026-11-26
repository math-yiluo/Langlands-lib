# The twisted trace of a compact double-coset indicator

The module `Langlands.BaseChange.DoubleCosetTwistedTrace` computes the
integrated action of the indicator of a compact double coset `I t I` on
`I`-fixed vectors. It then computes the twisted trace of that indicator. The
results concern a topological group `G` and a complex representation `ρ`, with
independent group and carrier universes, under the hypotheses stated for each
result below.

## The subgroup `I ∩ t I t⁻¹`

Let `G` be a topological group. For an open subgroup `I` and `t ∈ G`,
`conjIntersectionSubgroup I t` is the subgroup of `I` of the elements `k` with
`t⁻¹ k t ∈ I`, that is `I ∩ t I t⁻¹` viewed inside `I`
(`mem_conjIntersectionSubgroup` is definitional).

- `finite_quotient_conjIntersectionSubgroup`: if `I` is compact, the coset
  space `I ⧸ (I ∩ t I t⁻¹)` is finite. The subgroup is the preimage of the open
  set `I` under the continuous map `k ↦ t⁻¹ k t`. An open subgroup of a compact
  group has finite index.
- `natCard_quotient_conjIntersectionSubgroup`: if `K`, `N`, `M`, `Nbar`, `g`
  satisfy `Jacquet.IsIwahoriContraction K N M Nbar g` and `M` normalizes `N`,
  then the number of cosets of `K ∩ g K g⁻¹` in `K` is the published Iwahori
  index `Jacquet.iwahoriIndex K N g = [K ∩ N : g (K ∩ N) g⁻¹]`. The map
  `u ↦ u (K ∩ g K g⁻¹)` from `K ∩ N` descends to a bijection
  `(K ∩ N) ⧸ g (K ∩ N) g⁻¹ → K ⧸ (K ∩ g K g⁻¹)`.
  - It is well defined and injective by `Jacquet.mem_conjRadicalPiece_iff_of_mem`:
    for `x ∈ N`, `x ∈ g (K ∩ N) g⁻¹` exactly when `g⁻¹ x g ∈ K`.
  - It is surjective by the Iwahori factorization. Factor `k⁻¹ = l m u` with
    `l ∈ K ∩ Nbar`, `m ∈ K ∩ M` and `u ∈ K ∩ N`. Then
    `g⁻¹ (u k) g = (g⁻¹ m⁻¹ g)(g⁻¹ l⁻¹ g)` lies in `K` by the `levi` and `lower`
    contraction conditions, so `k` and `u⁻¹` have the same coset.

## The integrated indicator on fixed vectors

Let `G` be a Hausdorff topological group with its Borel σ-algebra, `μ` a
left-invariant measure, finite on compacts, `ρ` a smooth representation, `I` a
compact open subgroup, `t ∈ G`, and `v` an `I`-fixed vector. Write `k_q` for
the chosen representative of a coset `q ∈ I ⧸ (I ∩ t I t⁻¹)`.

- `integratedAction_doubleCosetIndicator_of_mem_fixedVectors`:
  `Π(1_{ItI}) v = μ(I) · ∑_q ρ(k_q t) v`. The left cosets `k_q t I` are pairwise
  disjoint and cover `I t I`. If `x = a t b` with `a, b ∈ I`, then `x ∈ k_q t I`
  exactly when `q` is the coset of `a`, by the defining property of
  `I ∩ t I t⁻¹`. On `k_q t I` the vector `ρ(x)v` equals `ρ(k_q t) v`. The published
  `Hecke.integratedAction_eq_sum_of_presentation` turns this finite indicator
  presentation into the sum. Each translate has measure `μ(I)` by left
  invariance (`measure_smul`).
- `averageMap_rho_eq_sum`: the compact average satisfies
  `e_I(ρ(t)v) = [I : I ∩ t I t⁻¹]⁻¹ ∑_q ρ(k_q t) v`. This is the published
  `Plancherel.averageMap_eq_finiteMean_cosets`, applied with the subgroup
  `I ∩ t I t⁻¹`, which fixes `ρ(t)v`.
- `integratedAction_doubleCosetIndicator_eq_smul_averageMap` combines the two:
  `Π(1_{ItI}) v = μ(I) [I : I ∩ t I t⁻¹] · e_I(ρ(t)v)`.
- `integratedAction_doubleCosetIndicator_averageMap`: for a Haar measure on a
  locally compact totally disconnected Hausdorff group, `Π(1_{ItI})` factors
  through `e_I`. By `Character.integratedAction_right_input_modular`,
  `Π(f)ρ(k) = Π(R_{k⁻¹} f)` for `k ∈ I`. The Renard modular function is trivial
  on the compact subgroup `I`, and the indicator is right `I`-invariant
  (`doubleCosetIndicator_mem`). The published `Jacquet.map_averageMap_of_forall_eq`
  then applies.

## The twisted trace

`twistedDistribution_doubleCosetIndicator`: let `G` be a locally compact,
totally disconnected Hausdorff topological group with its Borel σ-algebra, `μ` a
Haar measure on `G`, `I` a compact open subgroup, `t ∈ G`, `ρ` an admissible
complex representation, and `A` an endomorphism of `V` mapping `V^I` into
itself. Then

`twistedDistribution μ ρ hρ A (1_{ItI}) = μ(I) [I : I ∩ t I t⁻¹] · trace_{V^I}(A|_{V^I} ∘ C_t)`,

where `C_t = Jacquet.compressedAction ρ hρ I hI t` is `w ↦ e_I(ρ(t)w)` on `V^I`.
The operator `Π(1_{ItI}) A` factors as `V → V^I → V`: first `e_I ∘ A`, then
`w ↦ μ(I)[I : I ∩ t I t⁻¹] e_I(ρ(t)w)`, by the two preceding results. The
published `FiniteRankEnd.trace_eq_of_factorization` computes the finite-rank
trace on `V^I`. There `e_I(A(c · e_I ρ(t) w)) = c · A(e_I ρ(t) w)`, because `A`
preserves `V^I`.

## Provenance

These are derived steps of a compression proof of Henniart–Lemaire,
*Changement de base et induction automorphe pour GLₙ en caractéristique non
nulle*, Mém. SMF 124 (2011), I.5.3, Proposition, printed pp. 31–32 (PDF
pp. 39–40). They are the standard identity `1_{ItI} = vol(ItI) e_I * δ_t * e_I`
for compact double cosets, stated through compression operators. The printed
proof of I.5.3 takes a different route, through the Jacobian of an orbital
chart. Registered literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
