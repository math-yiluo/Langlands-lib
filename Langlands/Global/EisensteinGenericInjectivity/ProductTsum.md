# Finite products and determinants of absolutely convergent series

Module `Langlands.Global.EisensteinGenericInjectivity.ProductTsum` expands finite products and
determinants of absolutely convergent complex series as series over tuples of indices. The
module `Langlands.Global.EisensteinGenericInjectivity.Anchor` uses it to write the determinant
of a matrix of Eisenstein series as one absolutely convergent series over tuples of cosets.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`. Complete
types are printed by `PrettyPrinter.ppSignature` (the `#check` form), with the namespaces of the
page of `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

For families `f j : ι → ℂ`, `j : Fin m`, with `∑_c ‖f j c‖ < ∞`:

- `summable_prod_norm_pi`: the products `∏_j ‖f j (c j)‖` are summable over tuples
  `c : Fin m → ι`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.summable_prod_norm_pi.{u_1} {«ι» : Type u_1} {m : ℕ}
    (f : Fin m → «ι» → ℂ) :
    (∀ (j : Fin m), Summable fun c => ‖f j c‖) → Summable fun c => ∏ j, ‖f j (c j)‖
  ```
- `prod_tsum_eq_tsum_pi`: `∏_j ∑'_c f j c = ∑'_{c : Fin m → ι} ∏_j f j (c j)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.prod_tsum_eq_tsum_pi.{u_1} {«ι» : Type u_1} {m : ℕ}
    (f : Fin m → «ι» → ℂ) :
    (∀ (j : Fin m), Summable fun c => ‖f j c‖) →
      ∏ j, ∑' (c : «ι»), f j c = ∑' (c : Fin m → «ι»), ∏ j, f j (c j)
  ```

For a square family `T j k : ι → ℂ`, `j, k : Fin m`, of absolutely summable series:

- `det_tsum`: the determinant of the matrix of sums `∑'_c T j k c` is
  `∑'_{c : Fin m → ι} det (T j k (c j))`, the sum over tuples of row indices.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.det_tsum.{u_1} {«ι» : Type u_1} {m : ℕ}
    (T : Fin m → Fin m → «ι» → ℂ) (hT : ∀ (j k : Fin m), Summable fun c => ‖T j k c‖) :
    (Matrix.of fun j k => ∑' (c : «ι»), T j k c).det =
      ∑' (c : Fin m → «ι»), (Matrix.of fun j k => T j k (c j)).det
  ```
- `summable_norm_det_pi`: the terms `‖det (T j k (c j))‖` are summable over tuples.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.summable_norm_det_pi.{u_1} {«ι» : Type u_1} {m : ℕ}
    (T : Fin m → Fin m → «ι» → ℂ) (hT : ∀ (j k : Fin m), Summable fun c => ‖T j k c‖) :
    Summable fun c => ‖(Matrix.of fun j k => T j k (c j)).det‖
  ```

## Proofs

- `summable_prod_norm_pi` and `prod_tsum_eq_tsum_pi` are proved by induction on `m`. The step
  identifies `Fin (m + 1) → ι` with `ι × (Fin m → ι)` (`Fin.consEquiv`) and uses
  `Summable.mul_of_nonneg` and `tsum_mul_tsum_of_summable_norm`.
- `det_tsum` expands the determinant of the transpose over permutations (`Matrix.det_apply`);
  each signed product of series is a series over tuples by `prod_tsum_eq_tsum_pi`, and the
  finite sum over permutations commutes with the series (`Summable.tsum_finsetSum`).
- `summable_norm_det_pi` bounds `‖det‖` by the sum over permutations of the products of norms.

## Sources

Elementary analysis; no literature source.
