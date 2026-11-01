# Finite coset sums over a compact subgroup

Module `Langlands.Representation.GodementJacquet.WhittakerCosetSum`,
namespace `Langlands.GodementJacquet.CosetSum`.

Let `G` be a topological group and `μ` a left-invariant Borel measure on `G`
that is finite on compact sets. Let `K` be a compact subgroup and `K₀ ≤ K` an
open subgroup. The module proves that there are finitely many points
`k_1, …, k_m ∈ K` such that, for every function `f` on `G` that satisfies
`f(k k₀) = f(k)` for all `k ∈ K` and `k₀ ∈ K₀`,

`∫_K f dμ = Σ_i μ(K₀) · f(k_i)`.

This holds both for lower Lebesgue integrals of `[0, ∞]`-valued functions and
for Bochner integrals of complex-valued functions. For `GL_(n+1)` of a p-adic
field, it also proves that a full-matrix test function and a function on the
group that is right invariant under some open subgroup are both right
invariant under a single open subgroup of `GL_(n+1)(O)`.

## Source and provenance

The content is internal and derived. It is one step in reducing
`ModelWhittakerRationalityStatement` (convergence and rationality of every
full-matrix Whittaker integral on the coefficient model) to the torus
expansion of Whittaker functions and `FiniteFunctionMellinStatement`. After the
Iwasawa decomposition `G = N A K`, the Whittaker integral is an integral over
`K = GL_(n+1)(O)`. The integrand depends on `k` only through the right
translates `ρ(k)W` and `Φ(· k)`, which are invariant under a common open
subgroup `K₀`. This module turns the `K`-integral into a finite sum over the
cosets `K/K₀`, so the torus expansion is applied to finitely many vectors. The
reduction follows the standard argument for the convergence of these integrals
(Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer.
J. Math. 105 (1983), Section 2). The Lean statements here are general facts
about compact and open subgroups. The literature does not state them
separately.

## Declarations

Generic part (`section Generic`):

- `exists_finset_leftCosets K K₀ hK hK₀ hle`: a finite set `S ⊆ K` whose left
  cosets `k K₀` (`k ∈ S`) are pairwise disjoint and cover `K`. Proof: `K` is a
  compact space, so the open subgroup `K₀ ∩ K` of `K` has finite index
  (`Subgroup.quotient_finite_of_isOpen`). `S` is the image of the chosen
  representatives `Quotient.out`. Disjointness uses `QuotientGroup.eq`, and the
  covering uses `QuotientGroup.mk_out_eq_mul`.
- `exists_cosetSum μ K K₀ hK hK₀ hle`: the finite coset sum above, with the
  same `S` for both kinds of integral. Proof: split `∫_K` over the disjoint
  measurable cosets (`lintegral_biUnion_finset`, `integral_biUnion_finset`).
  On `k K₀` the function is the constant `f(k)`, and `μ(k K₀) = μ(K₀)` by left
  invariance (`measure_smul`). `μ(K₀) < ∞` because `K₀ ⊆ K` is contained in a
  compact set, which gives the integrability of each piece.

p-adic part (`namespace Padic`, with the canonical local instances of a
`PadicField`: topology, valuative relation and local field structure):

- `exists_nhds_matrixTest_rightInvariant Φ`: a neighborhood `U` of `1` in
  `GL_(n+1)(F)` with `Φ(M g) = Φ(M)` for all `g ∈ U` and all matrices `M`.
  Proof: `(g, M) ↦ Φ(M g) − Φ(M)` is locally constant, so its zero fiber is
  open. The generalized tube lemma, applied to `{1} × tsupport Φ`, gives `U`
  with `Φ(M g) = Φ(M)` for `M` in the support. Replacing `U` by `U ∩ U⁻¹`
  covers `M` outside the support: if `M g` is in the support, apply the
  previous case to `g⁻¹`; otherwise both values are `0`.
- `isCompact_integralSubgroup`, `isOpen_integralSubgroup`: the integral
  subgroup `GL_(n+1)(O)` (`Conductor.integralSubgroup`) is compact and open.
- `exists_openSubgroup_rightInvariant Φ W L hW`: for a test function `Φ` and a
  function `W` on the group that is right invariant under an open subgroup
  `L`, an open subgroup `K₀ ≤ GL_(n+1)(O)` such that every `k ∈ K₀` satisfies
  `Φ(M k) = Φ(M)` for all `M` and `W(g k) = W(g)` for all `g`. Proof: apply
  `generalLinearCompactOpen` of the canonical topological data to the
  neighborhood `U ∩ L ∩ GL_(n+1)(O)` of `1`.
