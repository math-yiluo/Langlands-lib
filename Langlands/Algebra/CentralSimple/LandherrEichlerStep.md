# Algebraic identities for the reduction to relative reduced norm one

Module: `Langlands.Algebra.CentralSimple.LandherrEichlerStep`.

Setting: `E/F` separable quadratic with `CharZero F`, `B` a finite-dimensional central simple
`E`-algebra, `relNorm F E B R : R ⊗_F B → E ⊗_F R` the relative reduced norm, `σ = tensorConj`
and `qm p q = 1 ⊗ p + r ⊗ q` (module
`Langlands.Algebra.CentralSimple.LandherrTensorQuadratic`).

- `relNorm_mul`, `relNorm_one`, `isUnit_relNorm`: the relative reduced norm is
  multiplicative, sends `1` to `1` and units to units.
- `map_qm`: `id ⊗ φ` sends `qm p q` to `qm (φ p) (φ q)`.
- `tmul_one_mul_tensorConj`: `(t ⊗ 1) σ(t ⊗ 1) = (t σ(t)) ⊗ 1`.
- `exists_hilbert90_point`: over a field `K`, if `δ σ(δ) = (t₀ ⊗ 1) σ(t₀ ⊗ 1)` with
  `t₀ ≠ 0`, then `δ σ(ω) = (t₀ ⊗ 1) ω` for some unit `ω = qm P Q`; apply `exists_hilbert90`
  to `c = δ (t₀⁻¹ ⊗ 1)`, which has `c σ(c) = 1`.
- For a number field `F` and `τ` acting on `E` by the conjugation:
  - `relNorm_mul_conj_of_eq`: if `1 ⊗ y = x τ_R(x)` in `R ⊗_F B` and
    `relNorm F (1 ⊗ y) = qm a₀ 0`, then `relNorm R x · σ(relNorm R x) = qm a₀ 0` in
    `E ⊗_F R` (naturality of `relNorm` along `F → R`, multiplicativity, and
    `relNorm (τ_R x) = σ(relNorm x)` from `relNorm_baseChange`, module
    `Langlands.Algebra.CentralSimple.LandherrNumberFieldNorm`);
  - `exists_relNorm_eq_qm`: for `τ y = y`, `relNorm F (1 ⊗ y) = qm a₀ 0` for some `a₀ ∈ F`:
    writing it as `qm p q`, `relNorm_baseChange` gives `qm p q = qm p (-q)`, so `q = 0`.

## Provenance

These are the algebraic identities behind the first step of the proof of Landherr's theorem
in Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.5, printed p. 77
(PDF p. 83): for symmetric `y`, a local solution `y = x_v τ(x_v)` gives
`Nrd(y) = N(x_v) σ(N(x_v))`, so `Nrd(y)` is a local norm from `E` at every place.
