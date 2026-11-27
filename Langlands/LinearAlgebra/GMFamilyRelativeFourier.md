# Fourier integrals with the phase `e^{i⟪x, H⟫}`, coordinates and decay integrals

Module `Langlands.LinearAlgebra.GMFamilyRelativeFourier` collects the analysis
on a finite-dimensional real inner product space `V` with its Euclidean volume
that the proof of Lapid's Lemma 8 uses on `V = 𝔞_M^G`.

## Results

- `phaseFourier u H = ∫ u(x) e^{i⟪x, H⟫} dx`, with
  `phaseFourier_eq_fourier`: it is Mathlib's Fourier transform `𝓕 u` (phase
  `e^{−2πi⟪x, ξ⟫}`) at `ξ = −H/(2π)`.
- `exists_phaseFourier_decay`: for every `N` there are `K`, `C` with
  `(1 + ‖H‖)^N ‖phaseFourier u H‖ ≤ C · schwartzSup K u` for all Schwartz `u`
  and all `H`. The Fourier transform is a continuous linear map of the
  Schwartz space (`SchwartzMap.fourierTransformCLM`), so its seminorms are
  bounded by finitely many seminorms of `u` (`exists_schwartzSup_bound_schwartz`
  of `GMFamilySchwartzExtension`), and
  `(1 + ‖w‖)^N |𝓕u(w)| ≤ 2^N · schwartzSup N (𝓕u)`
  (`SchwartzMap.one_add_le_sup_seminorm_apply`).
- `integral_phaseFourier` (Fourier inversion at the origin):
  `∫ phaseFourier u H dH = (2π)^{dim V} u(0)`, from Mathlib's inversion
  `Continuous.fourierInv_fourier_eq` and the change of variables
  `H ↦ −H/(2π)`.
- `volume_pi_eq_basisFun_addHaar`, `integral_eq_gramVolume_mul`: for a basis
  `b` of `V`, `∫_V g = gram(b) · ∫_{ℝ^ι} g(∑ X_i b_i) dX`, where `gram(b)` is
  the Library's `gramVolume` (the volume of the parallelepiped of `b`,
  `gramVolume_eq_abs_det`).
- `integrable_decay_weight`: for `c₀ > 0`, `(1 + c₀‖X‖)^{−(|ι|+1)}` is
  integrable on `ℝ^ι` (`integrable_one_add_norm`).
- `exists_integral_decay_bound`: for `c₀ > 0` and `n` there is `C ≥ 0` such
  that, for all `A ≥ 0`, `s ≥ 0` and `y₀`, whenever
  `|F(X)| ≤ A (1 + c₀ max(s, ‖X − y₀‖))^{−(n+|ι|+1)}` on a measurable set `D`,
  `|∫_D F| ≤ C A (1 + s)^{−n}`. The bound splits into
  `(1 + c₀ s)^{−n}`, at most `max(1, c₀⁻¹)^n (1 + s)^{−n}`, and the
  integrable weight translated by `y₀`.

## Provenance

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), §7, proof of Lemma 8,
pp. 326–327, and (17) (`∫ φ_P(H) dH = d_P(0)`)
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`).
`phaseFourier` is Lapid's `φ` for the measure `dx` (his `dλ` is
`(2π)^{−dim V} dx`, see `GMFamilyOrthogonalSetLimitStatement`). The results
are standard Fourier analysis, derived from Mathlib.
