# Kostant's theorem for `∏ᵢ 𝔤𝔩_{n i}(ℂ)` (assembly)

`maximallyFaithful_of` assumes `NilpotentConeIdealStatement n` and `OrbitVanishingStatement n`.
It proves `IsMaximallyFaithful π` for every representation `π` of `GLProd ℂ n` that has an
infinitesimal character and a nonzero Whittaker functional with nonzero coefficients. This is
the route of Matumoto (1987, §2) to Kostant's Theorem D/3.9.

## Auxiliary results

* `homogeneousComponent_mul_of_isHomogeneous`: for `g` homogeneous of degree `e`, the
  degree-`d` component of `f g` is the degree-`(d - e)` component of `f` times `g`, or `0` if
  `e > d`.
* `symbol_isHomogeneous`: `σ_N(P)` is homogeneous of degree `N` for `P ∈ U_N`.
* `exists_symbol_eq`: every homogeneous polynomial of degree `m` is `σ_m` of an element of
  `U_m`, namely the corresponding combination of ordered monomials.
* `gens j` is the generator `χ_{i,k}` of `charpolyIdeal` (`charpolyIdeal_eq`). It is
  homogeneous of degree `genDeg j = n i - k ≥ 1`; this follows from Mathlib's
  `Matrix.charpoly.univ_coeff_isHomogeneous` after renaming variables (`gens_isHomogeneous`).
  It is the symbol of the central element `zk i (n i - k)` (`symbol_zk_gens`).

## The induction (`mem_centralIdeal_of`)

We prove that every `P ∈ U_N` acting by `0` lies in `centralIdeal n π`, the left ideal generated
by the central elements acting by `0`, by strong induction on `N`.

* `N = 0`: then `P` is a scalar acting by `0`, so `P` is itself a generator.
* `N = M + 1`:
  1. Let `W` be the space of the symbols `σ_N(Q)` of the elements `Q ∈ U_N` acting by `0`.
     `W` is stable under `coadDer (E i a b)`, because
     `σ_N(xQ - Qx) = coadDer x (σ_N Q)` (`symbol_commutator`, `coadDer_ξ`) and commutators
     stay in `U_N` and in the annihilator. `W` vanishes at the Whittaker point
     (`eval_symbol_eq_zero`). By the orbit statement, `σ_N(P)` vanishes at all nilpotent
     tuples; by the nilpotent cone statement, `σ_N(P) = ∑_j f_j χ_j`.
  2. Taking degree-`N` components gives `σ_N(P) = ∑_j a_j χ_j`, where `a_j` is homogeneous of
     degree `N - genDeg j` (and `a_j = 0` if `genDeg j > N`). Choose `A_j ∈ U_{N - genDeg j}`
     with `σ(A_j) = a_j`.
  3. Let `c_j` be the scalar by which `Z_j = zk …` acts, and put `R = ∑_j A_j (Z_j - c_j)`.
     Then `R` lies in the ideal and in `U_N`, acts by `0`, and has `σ_N(R) = σ_N(P)`: the term
     `σ_N(A_j c_j)` vanishes because `A_j ∈ U_{N-1}`.
  4. By `mem_degreeFiltration_of_symbol_eq_zero`, `P - R ∈ U_M`, so `P - R` lies in the ideal
     by the induction hypothesis, and hence so does `P`.

Every `u ∈ U` lies in some `U_N` (Library `exists_mem_degreeFiltration`), so
`maximallyFaithful_of` follows.
