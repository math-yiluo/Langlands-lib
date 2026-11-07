# Continuity of roots over a henselian field algebraically closed in its completion

Author: Worker 105.

Internal infrastructure for the proof of Conrad's Corollary 5.12
(`HenselianFinitePointProperStatement`). Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed p.20, reduces to complete fields and then cites
"continuity of roots" ([BGR, 3.4.1/2]). The Lean proof does not pass to the completion. It
uses instead the statement below over `K` itself, whose formulation and proof are the
author's own. All names are in the namespace
`Langlands.AlgebraicGeometry.PointTopology.HenselianRootContinuity`.

Throughout, `K` is a nontrivially normed field and `K̂ = UniformSpace.Completion K`.

## Statements

- `norm_le_of_isRoot`: Cauchy's bound. A root `t` of a monic polynomial `p` satisfies
  `‖t‖ ≤ max 1 (∑_{n < natDegree p} ‖p.coeff n‖)`.
- `abv_prod_sub`, `pow_card_le_prod`: for an absolute value `v` on a field `L`, `a ∈ L` and a
  multiset `s`, `v (∏_{ρ ∈ s} (a - ρ)) = ∏_{ρ ∈ s} v (a - ρ)`. If `0 ≤ c ≤ v (a - ρ)` for all
  `ρ ∈ s`, then `c ^ card s ≤ ∏_{ρ ∈ s} v (a - ρ)`.
- `exists_tendsto_root (hK : IsHenselianValuedField K) (hcl : algebraicClosure K K̂ = ⊥)`:
  let `l` be an ultrafilter on `ι` and `p : ι → K[X]` monic polynomials, all of the degree
  of a monic `p₀`, with `(p i).coeff n → p₀.coeff n` along `l` for every `n`. If `t i ∈ K` is
  a root of `p i` for every `i`, then there is a root `τ ∈ K` of `p₀` with `t i → τ`
  along `l`.

## Proof of `exists_tendsto_root`

1. By Cauchy's bound and convergence of the coefficients, eventually `‖t i‖ ≤ B` for a
   constant `B ≥ 1`. Writing `p₀(t i) = ∑_{n ≤ d} (p₀.coeff n - (p i).coeff n) t_i^n`, this
   gives `p₀(t i) → 0`.
2. Let `L = AlgebraicClosure K` and let `v` be the absolute value on `L` extending the norm
   of `K`, given by `hK`. Over `L`, `p₀ = ∏_{ρ} (X - ρ)` over its multiset of roots, which has
   `d = deg p₀ ≥ 1` elements (`d = 0` is impossible because the `p i` have roots). So
   `‖p₀(x)‖ = ∏_ρ v (x - ρ)` for `x ∈ K`.
3. For each `i` some root `ρ` minimizes `v (t i - ρ)`, and then
   `v (t i - ρ) ^ d ≤ ‖p₀(t i)‖`. The roots are finitely many, so the ultrafilter contains
   one of these sets (`Ultrafilter.finite_biUnion_mem_iff`). For that `ρ`,
   `v (t i - ρ) → 0` along `l`. By the triangle inequality for `v`, `t` is Cauchy along `l`.
4. In the complete field `K̂`, `t i → τ̂` for some `τ̂`, and `p₀(τ̂) = 0` by continuity of
   polynomial evaluation. So `τ̂` is algebraic over `K`, hence lies in
   `algebraicClosure K K̂ = ⊥`, that is, `τ̂ = τ` for some `τ ∈ K`. Since `K → K̂` is an
   embedding, `t i → τ` in `K`, and `p₀(τ) = 0` by injectivity.

All proofs use only the standard axioms.
