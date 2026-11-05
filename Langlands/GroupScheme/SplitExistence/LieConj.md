# Conjugating root operators by root exponentials

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.LieConj`, namespace `LieRootData`.

## Declarations

- `V R T`: the `R`-span of the root operators `E_θ` for `θ` in a set of roots `T`, with
  `E_mem_V` and `V_mono`.
- `lie_E_E`: the integral bracket relation `lie_e_e`, transported to matrices over `R`.
- `sigma_E` (`R` a `ℚ`-algebra, `h : X →+ ℤ` positive on the roots `k` and `η`): for every
  `m`, `σ_m(E_η)` (coefficients of conjugation by `x_k`) is either `0` or `q • E_θ` for some
  `q ∈ R` and some root `θ` with `root θ = root η + m • root k`.
- `conj_sub_mem`: `x_k(g) E_η x_k(-g) - E_η` lies in the span of the `E_θ` with
  `root θ = root η + m • root k` and `m ≥ 1`.
- `conj_mem`: let `h` be positive on `k` and on every root of `T`, and let `T` be closed under
  adding positive multiples of `root k`. Then conjugation by `x_k(g)` maps the span `V R T` to
  itself.

Proofs: `sigma_E` is an induction on `m` using the recursion `sigma_succ` (module
`LieRootData`). Dividing by `m + 1` needs the `ℚ`-algebra structure. The bracket
`[E_k, E_θ]` is computed by `lie_E_E`, which applies because `root θ ≠ -root k`: `h` is
positive on `root θ = root η + m • root k`. `conj_sub_mem` sums `sigma_E` over `m ≥ 1` in the
expansion `conj_eq_sum`. `conj_mem` is an induction over the span, using `conj_sub_mem` for
the generators.

Provenance: internal. It is the classical computation of `Ad(x_k(g)) E_η` from the structure
constants of a Chevalley basis (Steinberg, *Lectures on Chevalley groups*, §§1–3), carried out
over a `ℚ`-algebra with the weak form `lie_e_e` of the bracket relation.
