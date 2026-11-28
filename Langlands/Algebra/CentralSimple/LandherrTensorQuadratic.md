# Coordinates on `E ⊗_F R` and multiplicative Hilbert 90

Module: `Langlands.Algebra.CentralSimple.LandherrTensorQuadratic`.

Let `E/F` be a separable quadratic extension with `CharZero F`, `r = skewRoot F E` and
`d = skewSq F E = r²` (module `Langlands.Algebra.CentralSimple.LandherrQuadraticData`), and
let `R` be a commutative `F`-algebra.

- `qm F E R p q = 1 ⊗ p + r ⊗ q ∈ E ⊗_F R`.
- `skewCoord` (the coordinate functionals of `E` for the basis `1, r`) and `tensorCoord`
  (the induced maps `E ⊗_F R → R`) give `tensorCoord_qm`, `qm_injective` and `exists_eq_qm`:
  every element of `E ⊗_F R` is `qm p q` for unique `p, q ∈ R`.
- Arithmetic: `qm_add`, `skewRoot_mul_tmul`,
  `qm_mul : qm p q · qm p' q' = qm (p p' + d q q') (p q' + q p')`,
  `tensorConj_qm : σ(qm p q) = qm p (-q)`, `qm_one`, `one_tmul_eq_qm`, and
  `qm_mul_tensorConj : qm p q · σ(qm p q) = qm (p² - d q²) 0`.
- `isUnit_qm_of_norm_ne_zero`: over a field `K`, `qm p q` is a unit when
  `p² - d q² ≠ 0`, with inverse `qm (p/N) (-q/N)`.
- `exists_hilbert90`: over a field `K`, if `c σ(c) = 1` then there are `P, Q` with
  `ω = qm P Q` a unit and `ω = c σ(ω)`.

## Proof of `exists_hilbert90`

Write `c = qm p q`, so `p² - d q² = 1`. If `p + 1 ≠ 0`, take `ω = qm (1 + p) q`: its norm is
`2(p + 1) ≠ 0` and `c σ(ω) = ω` by `qm_mul` and the norm equation. If `p = -1`, take
`ω = qm (-d q) (1 - p)`, whose norm is `d · 2(p - 1) = -4d ≠ 0`.

## Provenance

These are the coordinates `E ⊗_F R = R ⊕ R r` of a quadratic extension and the explicit form
of Hilbert's Theorem 90 for the étale quadratic algebra `E ⊗_F K` over a field `K`
(`c = ω / σ(ω)` with `ω = 1 + c` in the generic case). They are used in the reduction of
Landherr's theorem to the case of relative reduced norm one.
