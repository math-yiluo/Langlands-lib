# The algebraic core of the irreducibility of `GL_2(ℂ)` principal series

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoIrreducibleCore` (namespace
`Langlands.Archimedean.GLTwoCore`). Worker 728 wrote it for the proof of
`ComplexGLTwoUnlinkedIrreducibleStatement` (the target of Task 7148; written under Task 7064).

Provenance: internal, derived. It is the classical `U(2)`-type argument for `GL_2(ℂ)` (as in
Gelfand–Naimark and Želobenko), formulated with the explicit operators of `ComplexGLTwoModel`.

## Definitions

For `m₀ : ℤ` and `A : ℂ`, the level `j` has bidegree `(la m₀ j, lb m₀ j) = (m₀⁺ + j, m₀⁻ + j)`
(`m₀⁺ = m₀.toNat`, `m₀⁻ = (-m₀).toNat`) and exponent `ls A m₀ j = A - la m₀ j`.
`Setup ds Φ A m₀` collects the following hypotheses:

* `hΦ`, `hΦ0`: `Φ` is real differentiable and nonzero on `ℂˣ`;
* `hF1`: every `x` in the `U(2)`-finite functions `KF2 ds` satisfies
  `IsRealized Φ (ls A m₀ J) P x` for some `J` and some `P ∈ Eig (la m₀ J) (lb m₀ J)`;
* `hup`: `ls A m₀ j ≠ 0` for all `j`;
* `hdown`: `A + lb m₀ j + 1 ≠ 0` for all `j ≥ 1`.

`lev Φ A m₀ W j` is the space of polynomials realized at level `j` by elements of `W`.

## Main results

* `Setup.eq_top`: under `Setup`, every nonzero subspace `W` of `KF2 ds` stable under all
  `complexStandardLie 2 ds Y` is `⊤`.
* `Setup.isIrreducible`: under `Setup`, if `KF2 ds` is nontrivial, then
  `IsIrreducibleGKModule (complexStandardRep 2 ds) (complexStandardLie 2 ds)`.

## Proof

* `isRealized_cas_sub`: `casOp - casValue_{j+1}` sends a vector realized at level `j+1` by `P` to a
  vector realized at level `j` by `-4 Lap P` (`Cas_eq`).
* `descent` (strong induction on the level): a nonzero `x ∈ W` at level `J + 1` either gives a nonzero
  `casOp x - casValue x` at level `J`, or is harmonic (`Lap P = 0`, by injectivity). In the harmonic
  case `down_move` applies `(casOp - casValue_{J+1})(casOp - casValue_{J+2})` to `π(hol E) x` for
  `E ∈ {E01, E10, Ed}`. The result is realized at level `J` by `16 · 2(A + b + 1) · G` with
  `G ∈ {∂_{z₁}∂_{w₀}P, ∂_{z₀}∂_{w₁}P, ∂_{z₀}∂_{w₀}P - ∂_{z₁}∂_{w₁}P}` (`Lap_Lap_holMove`). By
  `exists_traceless_ne_zero` and `hdown` one of them is nonzero.
* `bottom`: a nonzero vector of `W` at level `0` makes `lev W 0 ∩ Eig a₀ b₀` a nonzero subspace
  stable under `D 0 1`, `D 1 0` (moves `k01`, `k10`), hence all of `Eig a₀ b₀`
  (`Eig_le_of_stable_left/right`, as `a₀ = 0` or `b₀ = 0`).
* `generation`: if level `j` is in `W`, then for `R` at level `j`, `π(antihol E)` gives
  `s_j (antiZ E) R + N (antiT E) R`. The second term is already in `W` at level `j + 1`. Since
  `s_j ≠ 0` (`hup`), this gives `z₁w₀R`, `z₀w₁R`, `(z₀w₀ - z₁w₁)R`, and with `N R` all `z_k w_i R`.
  By `mem_span_zw` this is all of level `j + 1`.
* `Setup.eq_top`: by `hF1`, a nonzero `x ∈ W` sits at some level. `descent`, `bottom` and `generation`
  put every level in `W`. By `hF1` again, every element of `KF2 ds` is in `W`.
