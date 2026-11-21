# Gaussian moment detection for the real compact Godement pairings

This module shows that polynomial Gaussian tests detect the compact Godement pairings at the real place. It is the real counterpart of the published `ComplexGodementGaussianPairing`. Instead of a sufficiently large unspecified bound, it uses the explicit convergence half-plane of the published `realGodementSchwartzMajorant`.

## Setting

Fix `m`, a Haar measure `μ` on `GL(m, ℝ)`, character data `c`, a list `ds` of real blocks, and `f` in the lower position principal series `principalSeries ℝ m (realPositionCharacter ds)`. Assume the half-plane condition

`m + normExponent (realPositionExponent ds) m i ≤ Re c.exponent + (m + 1)/2` for every `i : Fin m`.

The published `sectionValue μ c f Φ g` is the real Godement section

`determinantWeight c (m/2) g · ∫ f(h⁻¹) · determinantWeight c ((m+1)/2) h · Φ(h · lastRows g) dμ(h)`

(`sectionValue_eq_integral`, true by definition). Here `rowPoint h g = h · lastRows g`.

## Statement

`RealGodementGaussianPairingStatement`: under these hypotheses, let `κ` be any finite measure on the orthogonal group `K = unitaryCompact ℝ (m+1)` with a Borel measurable structure, and let `w : K → ℂ` be continuous.

1. For every Schwartz test `Φ` on `Matrix (Fin m) (Fin (m+1)) ℝ`, the function `k ↦ w k · sectionValue μ c f Φ k` is `κ`-integrable.
2. Suppose `∫ w k · sectionValue μ c f (gaussianPolynomial P) k dκ = 0` for every complex polynomial `P` in the entries. Then `∫ w k · sectionValue μ c f Φ k dκ = 0` for every measurable, compactly supported and bounded `Φ`.

`realGodementGaussianPairing` proves it.

## Proof

- `compactSample (k, h) = h · lastRows k` is continuous on `K × GL(m, ℝ)`. The joint weight is `jointWeight (k, h) = w k · determinantWeight c (m/2) k · f(h⁻¹) · determinantWeight c ((m+1)/2) h`. It is continuous.
- `compact_pairing_product`: if `(k, h) ↦ Φ(compactSample (k, h)) · jointWeight (k, h)` is integrable for `κ × μ`, then Fubini gives the integrability in part 1 for this `Φ`. It also writes the compact pairing as the product integral.
- `integrable_schwartz_joint`: for Schwartz `Φ` the product integrand is integrable. Apply `realGodementSchwartzMajorant` to the compact set `T` of orthogonal matrices. It gives one `μ`-integrable `b` with `‖f(h⁻¹)‖ · ‖determinantWeight c ((m+1)/2) h‖ · ‖Φ(h · lastRows k)‖ ≤ b h` for all `k ∈ K`. Multiply by the bounded continuous factor in `k`, and use `Integrable.mul_prod` and continuity.
- Part 1 follows. For part 2, move the sample matrix to the Euclidean space with `p = matrixEuclidean ∘ compactSample`. The half-Gaussian case of `integrable_schwartz_joint` shows that `exp(−‖p‖²/2) · jointWeight` is integrable.
- For a continuous linear functional `L` on the Euclidean space and `j ≥ 0`, the function `L(p)^j · exp(−‖p‖²)` equals the polynomial Gaussian test of `(realLinearPolynomial (L ∘ matrixEuclidean))^j` at the sample matrix. By hypothesis and `compact_pairing_product`, all these Gaussian moments of `jointWeight` vanish.
- The published `integrable_mul_of_hasCompactSupport` and `integral_eq_zero_of_gaussian_moments` (`Langlands.Analysis.GaussianWeightedMoment`) then give integrability and vanishing of the product integral of `Φ ∘ compactSample` against `jointWeight`. Here `Φ` is transported to the Euclidean space, where it is measurable, bounded and compactly supported. `compact_pairing_product` turns this into the vanishing of the compact pairing.

## Provenance

This is an internal step: polynomial Gaussian sections are dense enough to detect compact pairings. It is used for the reduction to polynomial-times-Gaussian Schwartz tests in Jacquet, *Archimedean Rankin–Selberg integrals* (2009): convergence in Proposition 7.1(i), generation in Proposition 7.1(vi) (pp. 43 and 46–47), and the adjacent-rank use in Section 8.3 (pp. 58–60). The tests `gaussianPolynomial P` use the Gaussian `exp(−∑ᵢⱼ Aᵢⱼ²)`. Jacquet's standard tests (p. 10) use `exp(−π Tr(AᵀA))` instead, so the tests here are a rescaled analogue (see `RealGodementGaussianPolynomial`). The proof uses only this fixed scale and makes no use of Jacquet's normalization. It follows the published complex module `ComplexGodementGaussianPairing`.
