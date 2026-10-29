# Spectral finiteness of tower data

Module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicTowerFinite`,
namespace `Langlands.RankinSelberg.UnequalRankTower`.

This is a helper module for the proof of
`Langlands.RankinSelberg.UnequalRankMirabolicPairingRigidityStatement`
(JPSS 1983, Section 2.11, Lemma on printed p.399). It states no new
proposition. Its results are internal. They replace the step of JPSS that uses
finite length of the restriction of `η` to a mirabolic subgroup. Here the
needed finiteness comes from the published finiteness of the Jacquet module
of an admissible finitely generated representation,
`Langlands.Parabolic.jacquetCenterSpan`.

Notation is that of `UnequalRankMirabolicTower`: `P_j = mirabolic j F`,
`U_(N+1) = upperUnipotent (N + 1) F`, `θ_N = standardCharacter ψ N`,
`diag(g, I)` = `towerEmbedding h g`. `IsTower ψ η h ρ q` is the tower
structure of that module. `R(ρ) = MirabolicRigidity.radicalSpan ρ` is the
published span of the vectors `ρ(u(v)) x - x` over radical elements `u(v)` of
`P_j`. `leviScalar a` is the published element `diag(a I_j, 1)` of `P_j`.

## Polynomials

`comp_aeval`: if a linear map `f : M → M'` satisfies `f ∘ S = S' ∘ f` for
endomorphisms `S, S'`, then `f ∘ P(S) = P(S') ∘ f` for every complex polynomial
`P`. The proof is by induction on `P` (sums and monomials), using
`Module.End.commute_pow_left_of_commute` for powers.

## The block shape `(i + 1, N - i)`

For `h : i + 1 ≤ N`, `towerShape h : BlockShape (N + 1)` has two blocks, of sizes
`i + 1` and `N - i`.

- `towerShape_index_val` computes coordinates: entry `r` of block `0` is `r`, and
  entry `r` of block `1` is `i + 1 + r`. `towerShape_index_lt_iff`: a coordinate
  of block `b` is `< i + 1` exactly when `b = 0`.
- `towerShape_unipotent_entry`: an element `g` of the block unipotent subgroup has
  `g_(x,y) = δ_(x,y)` unless `x < i + 1 ≤ y`. The proof uses the published
  descriptions `BlockShape.mem_unipotentSubgroup_iff` and `BlockShape.mem_parabolic_iff`.
  Diagonal blocks are identities, and blocks below the diagonal vanish.
- `towerShape_mem_upperUnipotent` and `towerShapeUnipotent h u`: an element of the
  unipotent radical is upper unipotent. `isLeading_towerShapeUnipotent`: it is
  leading at level `i`, since its leading `(i+1)`-block is the identity.
- `towerShape_blockScalar`: the block scalar `diag(a I_(i+1), I_(N-i))` (published
  `BlockShape.blockScalar` with value `a` on block `0` and `1` on block `1`)
  equals `towerEmbedding h (leviScalar a)`, where `leviScalar a ∈ P_(i+1)`. The
  proof compares entries with `towerEmbedding_entry` and `levi_entry`.

## Tower data at a positive level

Let `IsTower ψ η h ρ q` hold with `h : i + 1 ≤ N` (so the level is `i + 1`).

- `standardCharacter_towerShapeUnipotent`: for `u` in the unipotent radical of
  `towerShape h`, `θ_N(u) = ψ(u_(i,i+1))`. Here `u_(i,i+1)` is the last entry of
  `towerColumn h u`. All other superdiagonal entries of `u` are `0` by
  `towerShape_unipotent_entry`.
- `IsTower.sub_mem_radicalSpan`: for `u` in this unipotent radical and `w ∈ W`,
  `q(η(u) w) - q(w) ∈ R(ρ)`. Proof: `exists_towerRadical_mul` (level `i`)
  factors `u = diag(u(c), I) · u'` with `c = towerColumn h u` and `u'` leading at
  level `i + 1`. By `standardCharacter_eq_mul` and the previous item,
  `ψ(c_i) θ_N(u') = ψ(c_i)`, so `θ_N(u') = 1`, because a unitary character value
  is nonzero. The `levi` and `unipotent` fields of `IsTower` then give
  `q(η(u) w) = ρ(u(c)) q(w)`, and `ρ(u(c)) q(w) - q(w)` is a generator of `R(ρ)`.
- `IsTower.exists_polynomial_of_finiteDimensional`: assume that the span of the
  operators `σ(blockScalarLevi a')`, with `a' : Fin 2 → Fˣ`, is
  finite-dimensional. Here `σ = Parabolic.leviCoinvariants (towerShape h) η|_P` is
  the published Levi action on the unnormalized Jacquet module of `η` for this
  shape. Then for each `a ∈ Fˣ` there is a nonzero `P ∈ ℂ[X]` with
  `P(ρ(leviScalar a)) y ∈ R(ρ)` for all `y ∈ A`.

  Proof. Let `S = σ(blockScalarLevi a₀)` with `a₀ = (a, 1)`. Every power `S^k`
  equals `σ(blockScalarLevi a₀^k)`, so the algebra `ℂ[S]` spanned by the powers
  lies in the given finite-dimensional span. Hence `S` is integral over `ℂ`
  (`IsIntegral.of_mem_of_fg`), and its minimal polynomial `P = minpoly ℂ S` is
  nonzero with `P(S) = 0`. The map `w ↦ q(w) mod R(ρ)` is invariant under the
  unipotent radical by `IsTower.sub_mem_radicalSpan`. So it factors through the
  Jacquet module (published `Jacquet.lift`) as a map `Q̄`. By
  `towerShape_blockScalar` and the `levi` field, `Q̄ ∘ S = ρ̄(leviScalar a) ∘ Q̄`,
  where `ρ̄` is the action induced on `A / R(ρ)` (`R(ρ)` is `P_(i+1)`-stable).
  Applying `comp_aeval` to `Q̄` and to the quotient map `A → A / R(ρ)` gives
  `P(ρ(leviScalar a)) q(w) ≡ Q̄(P(S) [w]) = 0` modulo `R(ρ)`. Since `q` is
  surjective, this proves the claim for every `y`.

## p-adic fields

`IsTower.exists_polynomial T`: for `F` a `PadicField p` with topology data `T`,
`η` admissible and irreducible, and `IsTower ψ η h ρ q` with `h : i + 1 ≤ N`, the
conclusion of `IsTower.exists_polynomial_of_finiteDimensional` holds for every
`a`. The finite-dimensionality hypothesis is the published
`Parabolic.jacquetCenterSpan` for the shape `towerShape h`. Its finiteness input
(finite generation of `η` as a module over the group algebra) is the published
`moduleFinite_asModule_of_isIrreducible`.
