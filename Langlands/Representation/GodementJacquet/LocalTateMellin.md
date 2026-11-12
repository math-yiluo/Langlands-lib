# Shell expansion of scalar Mellin integrals

This helper module is internal infrastructure for the proof of
`Langlands.GodementJacquet.LocalTateConductorStatement`. It expands the actual
scalar Mellin integral

`Z(Φ, η, s) = scalarMellinIntegral abv (localMultiplicativeHaar F) η 1 Φ s
            = ∫_{Fˣ} Φ(x) η(x) abv(x)^s d^×x`

as a sum over the shells of fixed order. It also gives a closed form on a right
half-plane. Here `η : Fˣ →* ℂˣ` is any continuous character, and the weight is
the target's weight one.

## Preliminaries

- `natCast_zpow_cpow_eq`: `(q^{-k})^{1·s} = X_s^k`, where
  `X_s = spectralPoint q s = q^{-s}`. This is a public copy of the private
  computation in `TateScalarMellin.lean`.
- `exists_eq_zero_of_notMem_ball`, `exists_eq_const_on_ball` and
  `exists_support_bounds`: every Schwartz--Bruhat `Φ` vanishes outside some
  `ϖ^A O` and equals `Φ(0)` on some `ϖ^M O`, and both bounds can be taken with
  `A ≤ M`. They follow from the coset expansion and the lattice invariance in
  `LocalTateLattice`.
- `ordShell k = {x ∈ Fˣ | ord x = k} = ϖ^k O^×`. The shells are open, compact,
  pairwise disjoint and cover `{x | x ∈ ϖ^A O}` for `k ≥ A`. On `ordShell k`,
  `abv x = q^{-k}`.

## Shell coefficients and the expansion

`shellCoeff η Φ k = ∫_{O^×} Φ(ϖ^k u) η(u) d^×u`. Left translation by `ϖ^k`
preserves `localMultiplicativeHaar F`. The published
`setIntegral_comp_mul_left_of_mem_iff` from `ValuationShellIntegrationProof`
transports the shell integral to `O^×`, and gives (`setIntegral_ordShell`)

`∫_{ordShell k} Φ η |·|^s d^×x = (η(ϖ) X_s)^k · shellCoeff η Φ k`.

`mellin_hasSum` covers `Φ` vanishing outside `ϖ^A O` and `s` with
`‖η(ϖ) X_s‖ < 1`. In that case the Mellin integrand is integrable on all of
`Fˣ` and

`Z(Φ, η, s) = ∑_{n ≥ 0} (η(ϖ) X_s)^{A+n} shellCoeff η Φ (A+n)`.

The proof bounds each shell's norm integral by `‖η(ϖ)X_s‖^k · B · E`. Here `B`
bounds `Φ` and `E` bounds `η` on the compact group `O^×`, and `O^×` has
multiplicative mass one. A geometric series dominates these bounds, so the
integrand is integrable on the union of the shells
(`integrableOn_iUnion_of_summable_integral_norm`). It vanishes off that union,
and `hasSum_integral_iUnion` gives the sum.

## Closed form

`shellCoeff_of_le`: for `k ≥ M`, `Φ(ϖ^k u) = Φ(0)`, so the coefficient is
`Φ(0) · [a = 0]`. Here `a` is the exact conductor of `η` and the unit integral
from `LocalTateHaar` is used.

`mellin_eq` then gives, for `‖η(ϖ) X_s‖ < 1`,

`Z(Φ, η, s) = ∑_{k=A}^{M-1} (η(ϖ)X_s)^k shellCoeff η Φ k
             + Φ(0) [a = 0] (η(ϖ)X_s)^M / (1 - η(ϖ)X_s)`.

The proof compares the tail of the series with a geometric series.

`norm_mul_spectralPoint_lt_one` shows `‖c X_s‖ < 1` whenever
`log_q ‖c‖ < Re s`. This gives the explicit half-plane of convergence.

## Provenance

This is the standard computation of Tate's local zeta integral by decomposing
`Fˣ` into the shells `ϖ^k O^×`, as in Tate's thesis (source `tate-1967-thesis`,
§2.4) and the survey cited in `LocalTateConductorStatement.md`. The
implementation is internal and makes no new original-source assertion.
