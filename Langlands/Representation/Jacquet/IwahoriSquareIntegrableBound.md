# Square integrability bounds Jacquet eigenvalues along weak contractions

Author: Worker 4712. Module
`Langlands.Representation.Jacquet.IwahoriSquareIntegrableBound`, namespace
`Langlands.Jacquet`. This is a supporting module for the necessity half of
Casselman's criterion (Renard 2026, VII.1.2). The module adds no definitions. It
uses `centralCell`, `iwahoriIndex` (`IwahoriCellVolume.md`),
`IsWeakIwahoriContraction` (`WeakIwahoriBasis.md`) and the joint eigen-coefficient
(`JointIwahoriEigenCoefficient.md`).

The coefficients are measured with the published
`UnitaryCentralCharacter.coefficientNorm ℓ v`, the function
`g Z(G) ↦ ‖ℓ(ρ(g) v)‖` on `G ⧸ Z(G)` (`MatrixCoefficient/ModuloCenter.lean`).

## Results

- `isOpen_centralCell`: the image of `K g K` in `G ⧸ Z(G)` is open.
- `weight_mul_enorm_sq_lt_one_of_memLp_cells`. Let `c` be a unitary central
  character of `ρ`, `x` a `K`-fixed vector, `ℓ` a `K`-invariant functional, and
  `h : ℕ → G` with pairwise disjoint cells `centralCell K (h n)`. Assume
  `haar (centralCell K (h n)) ≥ weight ^ n * C` with `C ≠ 0`, and
  `ℓ(ρ(h n) x) = μ ^ n * ν` with `ν ≠ 0`. If `c.coefficientNorm ℓ x` is in `L²`
  for `haar`, then `weight * ‖μ‖² < 1` (in `ℝ≥0∞`).
  Proof: the coefficient equals `μ ^ n ν` on all of `K h(n) K`, because `x` is
  `K`-fixed and `ℓ` is `K`-invariant. The published `countableCellLpLower`
  (`Analysis/CountableCellLpProof.lean`) bounds
  `∑ₙ ‖μ ^ n ν‖² haar(cell n)` by the finite `L²` integral. Each term is at
  least `(weight ‖μ‖²)^n ‖ν‖² C`. If `weight ‖μ‖² ≥ 1`, the geometric series
  `∑ (weight ‖μ‖²)^n` is `∞` and `‖ν‖² C ≠ 0`, a contradiction.
- `iwahoriIndex_mul_enorm_sq_lt_one` (main result). Let `K` be compact open, `N`
  closed, `M` normalizing `N` and `Nbar`, factorization in `Nbar · M · N` unique,
  and `Z(G) ≤ M`. Let `b` be an Iwahori contraction and `a` a weak Iwahori
  contraction for `(K, N, M, Nbar)`, commuting with each other and with every
  element of `M`, and let the `K`-fixed vectors of `ρ` be finite-dimensional.
  Assume every smooth coefficient of `ρ` is in `L²` on `G ⧸ Z(G)` for a unitary
  central character `c`. Let `w ≠ 0` be a `K ∩ M`-fixed vector of the ordinary
  Jacquet module `V_N` with `b · w = μb w` and `a · w = μa w`. If
  `iwahoriIndex K N a > 1`, then `iwahoriIndex K N a * ‖μa‖² < 1`.

## Proof of the main result

The joint eigen-coefficient gives `x`, `ℓ` with `ℓ(x) ≠ 0` and
`ℓ(ρ(a ^ n b) x) = μa ^ n (μb ℓ(x))`. As in `JointIwahoriEigenCoefficient`,
`μb ≠ 0`. Since `a ^ n b` is a weak contraction commuting with `M`, the
volume formula `measure_centralCell` and `iwahoriIndex_pow_mul` give

```text
haar (centralCell K (a ^ n b)) = iwahoriIndex K N a ^ n * (iwahoriIndex K N b * haar (image of K)).
```

The constant `iwahoriIndex K N b * haar(image of K)` is nonzero and finite. The
index is nonzero because `b (K ∩ N) b⁻¹` has finite index, and `haar(image of K)`
is positive and finite because that image is open and compact. Distinct `n` give
disjoint cells: by `centralCell_eq_of_not_disjoint`, meeting cells are equal, so
their volumes agree. That forces
`iwahoriIndex K N a ^ m = iwahoriIndex K N a ^ n`, hence `m = n` because the index
exceeds one. The previous lemma, with `h n = a ^ n b`, `weight = iwahoriIndex K N a`
and `ν = μb ℓ(x)`, gives the bound.

## Provenance

Derived. This is the converse argument at the end of the proof of Renard VII.1.2
(printed p.224 / PDF p.230): if an exponent violates the bound, choose `v` with
`j_N(v)` in the corresponding eigenspace and `λ` with `⟨j_N(v), j_N(λ)⟩ ≠ 0`. Then
`∑_z c |χ(z)|² = +∞`, where the volume factor `δ_P(z)` has been absorbed into the
normalized coefficient. The Lean version works with the unnormalized Jacquet
eigenvalue `μa` and keeps the volume factor `iwahoriIndex K N a` explicit. The
modulus comparison with the normalized exponent is in `IwahoriModulusIndex.md`.
The test elements are `a ^ n b` (powers of the weak contraction `a` times the
strict contraction `b`), not Renard's products `z ∈ S'_M(n)`. Source: David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`).
