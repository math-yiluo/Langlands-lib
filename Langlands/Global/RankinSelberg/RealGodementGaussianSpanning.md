# Spanning the real K-finite principal series by polynomial Gaussian Godement sections

This module proves that, in the real Godement convergence half-plane, the Godement sections of polynomial Gaussian tests with `K`-finite lower inputs span the whole `K`-finite upper position principal series. It is the real counterpart of the published `ComplexGodementGaussianSpanning`. It replaces that module's unspecified bound with the explicit half-plane of the published `realGodementSchwartzMajorant`.

## Definitions and statement

Fix `m`, a Haar measure `μ` on `GL(m, ℝ)`, character data `c` and a list `ds` of real blocks. Write `K = unitaryCompact ℝ (m+1)` for the orthogonal group.

- `sectionValue_mul_right`: for every test `Φ` and all `g, q ∈ GL(m+1, ℝ)`,
  `sectionValue μ c f Φ (g q) = determinantWeight c (m/2) q · sectionValue μ c f (x ↦ Φ(x q)) g`.
  This holds because `lastRows (g q) = lastRows g · q` and `determinantWeight` is multiplicative.
- `gaussianSections μ c ds` is the set of sections `sectionValue μ c f (gaussianPolynomial P)`. Here `P` is any complex polynomial in the entries of an `m × (m+1)` matrix, and `f` is any `K`-finite vector of the lower position principal series, `kFiniteFunctions (principalSeries ℝ m (realPositionCharacter ds)) (unitaryCompact ℝ m)`.
- `gaussianSection_mem_kFinite`: assume the half-plane condition
  `m + normExponent (realPositionExponent ds) m i ≤ Re c.exponent + (m+1)/2` for all `i`.
  If `f` is in the lower position principal series, then every polynomial Gaussian section lies in
  `kFiniteFunctions (principalSeries ℝ (m+1) (realPositionCharacter (.character c :: ds))) K`.

`RealGodementGaussianSpanningStatement`: under the half-plane condition, the complex span of `gaussianSections μ c ds` equals `kFiniteFunctions (principalSeries ℝ (m+1) (realPositionCharacter (.character c :: ds))) (unitaryCompact ℝ (m+1))`. `realGodementGaussianSpanning` proves it.

## Proof

- **Linearity.** The published majorant `realGodementSchwartzMajorant`, applied to `{g}`, makes the Godement integrand integrable for every Schwartz test. So `Φ ↦ sectionValue μ c f Φ` is complex-linear on Schwartz tests (`sectionLinear`).
- **Gaussian sections are `K`-finite.** Membership in the principal series is the published `realGodementSchwartzSection`. Let `k` be orthogonal. By `sectionValue_mul_right` and `rightTranslate_mem_range`, the right translate by `k` of the section of `gaussianPolynomial P` is a scalar multiple of the section of `gaussianPolynomial q`, with `q` in the finite-dimensional space of polynomials of total degree at most `totalDegree P`. So the span of right `K`-translates lies in the image of that space under a linear map. This gives `gaussianSection_mem_kFinite` and the inclusion of the span in the `K`-finite principal series.
- **Converse.** Let `F` be `K`-finite in the upper principal series. Restrict functions to `K` (`restrictK`) and use the Haar probability measure `haarK (m+1)` on `K`. Apply the published `compactPairingSpanning` to `restrictK F`. The family `S` consists of the restrictions of all Gaussian sections.
  - Every member of `S` has a finite-dimensional right span (`finiteDimensional_rightSpan_restrictK`). Its right translates are scalar multiples of members of `S`, by the polynomial translation law. So the right span stays in `span S`.
  - Integrability against continuous weights is part 1 of `realGodementGaussianPairing`.
  - Detection: let `w` be a continuous weight annihilating `S`. The published `realGodementFiniteGenerationKFiniteLower` puts `F` in `compactKFiniteLowerSectionSpan μ c ds`. Use induction on this span. For a generator `sectionValue μ c f Φ`, `f` is `K`-finite and `Φ` is smooth and vanishes outside a compact set, so `Φ` is measurable, bounded and compactly supported. Part 2 of `realGodementGaussianPairing` then gives a zero pairing. Sums and scalar multiples are handled by linearity of the integral. Integrability comes from continuity of members of the compact span: they are in the principal series by the published `compactSectionSpan_le_principalSeries`.

  Hence `restrictK F` lies in `span S`, which is the image under `restrictK` of the span of `gaussianSections` (`Submodule.map_span`). So some `F'` in that span has the same restriction to `K`. Both are in the upper principal series, so the Iwasawa decomposition `g = diag(a) · u · k` and left covariance give `F' = F` (`eq_of_restrictK`).

## Provenance

This is an internal step. It is the real version of the statement that `K`-finite vectors are sums of Godement sections with standard (polynomial times Gaussian) Schwartz functions, Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Proposition 7.1, used in Section 8.3. It is proved in the half-plane where the Godement integrals of Schwartz tests converge, and follows the published complex module `ComplexGodementGaussianSpanning`.
