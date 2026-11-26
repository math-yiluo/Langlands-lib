# The affine column Fourier transfer in the real larger-gap unfolding

This module is the real counterpart of the Library's `ComplexGapColumnFourier`.

Basic notation, for a unit `a : ℝˣ`:

* `piMeasure ι a` is the product over `ι` of the real self-dual measure `realSelfDualMeasure a`;
  it is an additive Haar measure, and `piMeasure_neg` shows it does not change under `a ↦ -a`.
* `psi a t` is the complex value of the positive real character `realScaledCharacter a` at `t`;
  `psi_neg` gives `psi (-a) t = psi a (-t)`, and `norm_psi`, `continuous_psi` record that it is
  unitary and continuous.
* `columnSchwartzFourier a Φ` is the positive real Fourier transform of a Schwartz function on
  `Fin m → ℝ`, again a Schwartz function; `columnSchwartzFourier_apply` identifies its values with the
  Library's `realFourierTransform a Φ`, written `𝓕_a Φ` below.
* For a decidable predicate `p` on the coordinates, `merge p x y` assembles a column from its
  coordinates `x` in `p` and `y` outside `p` (`merge_apply`, `merge_apply_left`,
  `merge_apply_right`, `continuous_merge`).

`columnSlices`: for a column Schwartz function `Φ`, a frequency `x₀` on the coordinates in `p` and a
position `y₀` on the others, the slice `x ↦ Φ (merge p x y₀) ψ_a(⟨x, x₀⟩)` and the Fourier-side slice
`y ↦ 𝓕_a Φ (merge p x₀ y) ψ_a(-⟨y, y₀⟩)` are integrable for the product self-dual measures and have equal
integrals. The proof identifies the two coordinate blocks with an orthogonal decomposition of
Euclidean space and applies the Library's partial Fourier inversion
`RealGodement.realGodementScaledProductFourier`; the product of the self-dual measures corresponds to
the scaled Euclidean volume.

`integral_mulVec` is the change of variables `x ↦ g x` for `g ∈ GL_{r+1}(ℝ)`: it multiplies the
integral by `|det g|^{-1}` (Mathlib's `Measure.map_linearMap_addHaar_eq_smul_addHaar`).
`fourier_pullColumn` deduces that the Fourier transform of `x ↦ Φ (g x)` at `y` is
`|det g|^{-1}` times the Fourier transform of `Φ` at `g^{-T} y`.

`RealGapColumnFourierStatement` (proved by `realGapColumnFourier`): for an invertible real
`(r+1) × (r+1)` matrix `g`, a Schwartz column test `Φ`, `α` on the coordinates in `p` and `β` on the
others, the functions

* `P x = Φ (g · merge p x β) · ψ_a(∑ x_i α_i)` and
* `Q y = 𝓕_a Φ (g^{-T} · merge p α y) · ψ_{-a}(∑ y_i β_i)`

are integrable for the product self-dual measures, and `∫ P = |det g|^{-1} ∫ Q`. It is
`columnSlices` for the pulled-back test combined with `fourier_pullColumn` and `psi_neg`.
`realGapColumnFourierProduct` applies it to a finite family of independent columns: the products are
integrable for the product measures and the integrals differ by `(|det g|^{-1})^{#J}` (Fubini for finite
products).

The complex statement has the normalized determinant `|det g|_ℂ = |det g|²`; over ℝ the normalized
absolute value is the ordinary one. This is the Fourier and determinant calculation inside the
coordinates of Lemma 10.2. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, Lemma 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
