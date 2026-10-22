# Explicit archimedean Gamma factors

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Archimedean.Definitions`.
It is moved from `Langlands.LocalFactor.Archimedean` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. Original source references and authorship below are retained.
Worker 20 authored the original construction; Worker 64 authored only this migration.
The [migration record](../Abelian/Definitions.md#structural-migration-record) gives the complete map and checks.


This module constructs the real and complex Gamma factors, spectral translates,
finite products, and Tate's standard abelian epsilon expressions. Gamma factors
are represented by nonzero entire reciprocal denominators and punctured
meromorphic germs. Numerical evaluation requires a proof that the input is
regular.

The original source is Tate, *Number theoretic background* (1979), section 3.1.1
through 3.1.2, printed pages 12–13, and section 3.2.4–3.2.5, printed page 13.
The retained PDF pages are 21–22. Both pages were visually read. The complex
case is printed with the label `(3.2.1)` at the top of page 13, in the sequence
of local abelian L-factor definitions; its context and formula identify it
unambiguously. Section 3.3.1, printed page 14, describes the later extension to
actual archimedean Weil representations by irreducible decomposition and
induction. That attachment is outside this analytic prerequisite.

Registered original: `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
retained at
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.

The exact normalizations are

```
Γ_R(s) = π^(-s/2) Γ(s/2),
Γ_C(s) = 2 (2π)^(-s) Γ(s).
```

In particular, the factor `2` in `Γ_C` is retained. The constructors reuse the
actual functions in pinned Mathlib `Analysis.SpecialFunctions.Gamma.Deligne`.
That file proves that their reciprocals are complex differentiable everywhere.
Their values at `s=1` prove that the entire denominators are not identically
zero. These intrinsic analytic proofs fill every field of `ReciprocalEntire`;
there is no assumption of an abstract Gamma-factor system.

Mathlib's total Gamma representative assigns zero at its poles. This module
does not expose that as an everywhere defined finite local factor. Instead,
the zero becomes a zero of the reciprocal denominator. The proved
`ReciprocalEntire.isPole_iff_no_analytic_germ` criterion shows that these points
are precisely singularities of the resulting punctured germ. The explicit pole
sets are `s=-2n` for `Γ_R` and `s=-n` for `Γ_C`, with `n` a natural number.
At regular points, the unit-valued evaluation agrees with the original
displayed formulas.

`GammaBlock` records a real or complex factor with an arbitrary complex spectral
translation. `gammaProduct` multiplies finitely many such actual factors.
Its construction proves that the denominator is nonzero as an entire function,
that products have the expected union of pole sets, and that reordering the
block list does not alter the factor. These blocks are analytic input data,
not stand-ins for actual Weil representations or an assumed classification.

The component wrappers follow Tate's original notation exactly:

| Input component | L-factor | Standard epsilon expression |
|---|---|---|
| `x^(-N) ω_(s+a)` over `R`, `N=0` or `1` | `Γ_R(s+a)` | `i^N` |
| `z^(-N) ω_(s+a)` over `C`, `N≥0`, chosen embedding | `Γ_C(s+a)` | `i^N` |

Here `ω_s` is Tate's norm quasicharacter. In the real epsilon formula the
additive character is `exp(2πix)` and the measure is Lebesgue measure. In the
complex epsilon formula the additive character is `exp(2πi Tr(z))` and the
measure is `i dz∧d(conj z)=2 da db`. The code constructs the indicated numbers
and proves nonvanishing by `i≠0`. It does not assert their functional equations,
nor a transformation formula for arbitrary additive characters or measures.
The component L-factor wrappers intentionally have no additional parity or
weight shift: the inverse algebraic character in Tate's notation already
accounts for it. No switch to a different parameter convention is implicit.

The direct project dependency is the same contribution's internal
[`Langlands.LocalFactor.Analytic.ReciprocalEntire`](../Analytic/ReciprocalEntire.md) pair. There are no imports of pending
nonarchimedean harmonic, class-field, or representation proofs. Attachment to
actual archimedean Weil groups and their representations belongs to the
coordinated global definition branch, task
`a6077a58-5c34-4ef4-9cd1-7e3d1b2332f4`; this arithmetic task owns these analytic
Gamma constructions. The representation attachment and its comparison laws
remain explicit outstanding obligations. This module does not establish the
archimedean correspondence or any global functional equation.
