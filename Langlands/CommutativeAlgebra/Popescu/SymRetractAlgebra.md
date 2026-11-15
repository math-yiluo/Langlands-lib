# The symmetric-algebra retract: definitions and basic facts

This module sets up the presentation of the algebra `C = Sym_B(I/I²)` from Stacks Project,
*Smoothing ring maps*, Lemma 3.1 (tag 07CE). Here `B = R[x_1, …, x_n]/I` and `I` is generated
by `f_1, …, f_m`. All declarations are in namespace `SymRetract`.

## Variables and derivatives

The polynomial ring `R[x_1, …, x_n, y_1, …, y_m]` is `MvPolynomial (Fin (n + m)) R`, with
`x_i = X (Fin.castAdd m i)` and `y_j = X (Fin.natAdd n j)`.

- `ιx`: the inclusion `R[x] → R[x, y]` (`rename (Fin.castAdd m)`).
- `yv j`: the variable `y_j`.
- `pderiv_rename_of_notMem_range'`: a renamed polynomial has zero derivative along every
  variable outside the range of the renaming.
- The partial derivatives of the generators:
  - `pderiv_x_ιx`: `∂/∂x_i (ιx p) = ιx (∂p/∂x_i)`;
  - `pderiv_y_ιx`: `∂/∂y_j (ιx p) = 0`;
  - `pderiv_x_yv`: `∂y_j/∂x_i = 0`;
  - `pderiv_y_yv`: `∂y_j/∂y_{j'} = δ_{jj'}`.

## The ideal of `Sym(I/I²)`

Let `K` be the module of relations among the `f_j` modulo `I²`, that is, the vectors
`κ ∈ R[x]^m` with `Σ_j κ_j f_j ∈ I²`.

- `symGen κ = Σ_j κ_j y_j`.
- `symIdeal I F = I · R[x, y] + (symGen κ : κ ∈ K)`. The quotient `R[x, y]/symIdeal I F` is
  `B[y]` modulo the linear forms coming from `K`. This is the symmetric algebra of
  `B^m / K ≅ I/I²`, as in the proof of Stacks Lemma 3.1.

The basic memberships:

- `ιx_mem_symIdeal`: `ιx(I) ⊆ J`;
- `ιx_mem_symIdeal_sq`: `ιx(I²) ⊆ J²`;
- `symGen_mem_symIdeal`: `symGen κ ∈ J` for `κ ∈ K`.

Finally, `pderiv_mem_of_mem_sq` says that partial derivatives of elements of `I²` lie in `I`.
This follows from the Leibniz rule on products `ab` with `a, b ∈ I`
(`Submodule.mul_induction_on`).

## Status

The module imports only Mathlib and uses only the standard axioms.
