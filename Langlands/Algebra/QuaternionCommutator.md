# Norm-one elements of quaternion division algebras as commutators

Module `Langlands.Algebra.QuaternionCommutator`, namespace `Langlands.CentralDivision`.

## Setting

`K` is a field and `D` is a finite-dimensional central division `K`-algebra (`K`, `D` in the
same universe). We write

* `P_a = reducedCharpoly K D a` for the Library's reduced characteristic polynomial;
* `Nrd(a) = reducedNorm K D K (1 ⊗ a)` for the reduced norm;
* `d = reducedDegree K D` for the reduced degree.

Several results assume `d = 2`, which is the case for quaternion division algebras
(`dim_K D = 4`).

## Definitions

* `reducedTrace K D a := -(coefficient of X^{d-1} in P_a)`, the **reduced trace** `Trd(a)`.

## Results

* `algebraMap_reducedTrace`: under the Library's chosen splitting chart
  `finiteGaloisSplittingChart K D`, `Trd(a)` maps to the matrix trace of the image of
  `1 ⊗ a`. This uses `reducedCharpoly_map_chart` and Mathlib's
  `Matrix.trace_eq_neg_charpoly_coeff`.
* `reducedTrace_add`, `reducedTrace_smul`, `reducedTrace_sub`: the reduced trace is `K`-linear.
* For `d = 2`:
  * `reducedCharpoly_coeff_zero`: the constant coefficient of `P_a` is `Nrd(a)`.
  * `reducedCharpoly_eq_quadratic`: `P_a = X² - Trd(a) X + Nrd(a)`.
  * `sq_sub_reducedTrace_add_reducedNorm` (Cayley–Hamilton): `a² - Trd(a) a + Nrd(a) = 0`.
  * `reducedTrace_one`: `Trd(1) = 2`.
* **`exists_mul_add_eq_conj`**: suppose `d = 2`, `z ∉ K` and `Nrd(a) = 1`. Then there are
  `s ∈ K` and a unit `y` with `a (z + s) = y (z + s) y⁻¹`. Equivalently,
  `a = y (z+s) y⁻¹ (z+s)⁻¹`.

## Proof of the main result

1. If `a = 1`, take `s = 0` and `y = 1`.
2. Otherwise `Trd(a - 1) ≠ 0`. Indeed, `Trd(a) = 2` together with `Nrd(a) = 1` would give
   `(a - 1)² = 0` by Cayley–Hamilton, hence `a = 1`.
3. Put `s = -Trd((a-1) z) / Trd(a-1)` and `x = z + s`. By linearity of the trace,
   `Trd(a x) = Trd(x)`. By multiplicativity of the reduced norm, `Nrd(a x) = Nrd(x)`. Hence
   `P_{ax} = P_x`.
4. Since `x ∉ K`, its minimal polynomial has degree `2`, so it equals `P_x`. In particular
   `a x` is a root of the minimal polynomial of `x`.
5. The two `K`-algebra embeddings of `AdjoinRoot (minpoly K x)` into `D`, sending the root to
   `x` and to `a x`, are conjugate by the Library's Skolem–Noether theorem
   `fieldEmbeddingsConjugate`. This gives `x = u (a x) u⁻¹`; take `y = u⁻¹`.

## Provenance

Internal; standard algebra of quaternion algebras. The main result is a commutator lemma of
Wang type (cf. S. Wang, *On the commutator group of a simple algebra*, Amer. J. Math. 72
(1950)), here proved only for reduced degree `2`, directly from the Library's
reduced characteristic polynomial and Skolem–Noether theorem. It is used for Task 5398: it
shows that every Levi element of reduced norm `1` is a product of Eichler transformations.

The constant-coefficient identity is reused as
`Langlands.CentralSimple.reducedCharpoly_coeff_zero_two` from
`Langlands/Algebra/ReducedCharpolyDivision.lean`.
