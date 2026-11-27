# Absolute convergence of the open-cell integral: the proof

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellConvergenceProof`.

`Langlands.Global.cuspidalPairEisensteinOpenCellConvergence` proves
`Langlands.Global.CuspidalPairEisensteinOpenCellConvergenceStatement.{u}` (module
`Langlands.Global.Factors.CuspidalPairEisensteinOpenCellConvergenceStatement`, see
[CuspidalPairEisensteinOpenCellConvergenceStatement.md](CuspidalPairEisensteinOpenCellConvergenceStatement.md)):
for a number field `F` with `[CompactSpace (AdeleQuotient F)]`, actual cuspidal realizations `T`,
`T'` of `GL_(r+1)` and `GL_(t+1)` with unitary central characters, a standard additive character
`ψ` and a section `φ` with `IsSection T T' φ`, there is `σ ∈ ℝ` such that for every `s` with
`σ < Re s` the open-cell integrand `openCellIntegrand ψ φ s` is integrable for
`openCellHaar F r t` (Borel σ-algebra on `M_((t+1)×(r+1))(𝔸)`).

The unitarity hypotheses are not used: the growth exponents of the cusp forms come from the
central characters that every irreducible realization has
(`OperatorRealization.existsUnique_hasCentralCharacter`).

## Proof

Let `D = (t + 1)(r + 1)` and let `d` be the real dimension of the archimedean coordinates of
`M_((t+1)×(r+1))(𝔸)` (`Module.finrank ℝ (EqualAnalytic.ArchRow F D)`).

1. **Pointwise bound.** `OpenCellPointwise.exists_norm_openCellIntegrand_le`
   ([CuspidalPairEisensteinOpenCellPointwise.md](CuspidalPairEisensteinOpenCellPointwise.md))
   gives `b ∈ ℝ` such that for `Re s + b ≥ 0` there is `C ≥ 0` with
   `|openCellIntegrand ψ φ s Y| ≤ C · Ω_(Re s + b)(Y)` for all `Y`, where `Ω_e` is the majorant
   `OpenCellMajorant.majorant e` of
   [CuspidalPairEisensteinOpenCellMajorant.md](CuspidalPairEisensteinOpenCellMajorant.md).
2. **Choice of `σ`.** `σ = max(d, D + 1) - b`. If `σ < Re s`, then `e = Re s + b` satisfies
   `d < e`, `D + 1 < e` and `e ≥ 0`.
3. **Measurability.** The integrand is continuous
   (`OpenCellContinuity.continuous_openCellIntegrand`,
   [CuspidalPairEisensteinOpenCellContinuity.md](CuspidalPairEisensteinOpenCellContinuity.md)),
   hence almost everywhere strongly measurable.
4. **Finite integral.** `openCellHaar F r t` is an additive Haar measure (it is `Measure.addHaar`
   for the Borel σ-algebra of the locally compact group `M_((t+1)×(r+1))(𝔸)`). By monotonicity of
   the lower integral, `∫⁻ ‖integrand‖ₑ ≤ ofReal(C) · ∫⁻ ofReal(Ω_e)`
   (`lintegral_const_mul'`), and `OpenCellMajorant.lintegral_majorant_lt_top` shows that
   `∫⁻ ofReal(Ω_e) < ∞` because `d < e` and `D + 1 < e`. No measurability of `Ω_e` is needed.

Steps 3 and 4 are the two conditions of `Integrable`.

## Helper modules

- [CuspidalPairEisensteinOpenCellLocalSum.md](CuspidalPairEisensteinOpenCellLocalSum.md): the
  local sums `∑_(y ∈ M(F_v)/M(𝒪_v)) max(1, ‖y‖)^(-β) ≤ 1 + 2 N(v)^(D - β)` for `β ≥ 0` with
  `N(v)^(D - β) ≤ 1/2`; both conditions hold when `β > D + 1`, since `N(v) ≥ 2`. Without a
  condition on `β` the sum can be infinite (for `β = 0` it counts the classes).
- [CuspidalPairEisensteinOpenCellMajorant.md](CuspidalPairEisensteinOpenCellMajorant.md): the
  majorant `Ω_β` and the finiteness of its lower integral for `β > max(d, D + 1)`.
- [CuspidalPairEisensteinOpenCellSliceBound.md](CuspidalPairEisensteinOpenCellSliceBound.md):
  the bound `|W_M(φ_s)(p k)| ≤ |δ_P(m)^(1/2 + s/N)| C |det m₁|^(β₁) |det m₂|^(β₂)`.
- [CuspidalPairEisensteinOpenCellDeterminant.md](CuspidalPairEisensteinOpenCellDeterminant.md):
  `|det m₂|^(-e) ≤ const · Ω_e(Y)` on the open cell, for `e ≥ 0`.
- [CuspidalPairEisensteinOpenCellPointwise.md](CuspidalPairEisensteinOpenCellPointwise.md): the
  pointwise majorant `C · Ω_(Re s + b)` of the integrand, for `Re s + b ≥ 0`.
- [CuspidalPairEisensteinOpenCellContinuity.md](CuspidalPairEisensteinOpenCellContinuity.md):
  continuity of the integrand.

## Provenance

F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`),
proof of Theorem 5.1, pp. 351–352 (PDF pages 56–57): at an archimedean place `v` the local
component of the Fourier coefficient is given by formula (4.2) of Shahidi, *Functional equation
satisfied by certain L-functions*, Compositio Math. 37 (1978)
(`shahidi-1978-functional-equation`), p. 187 (PDF page 18), with `s` changed to `-s`, and it
"converges absolutely for `Re(s)` large (it is dominated by the corresponding intertwining
integral which converges for `Re(s)` large)" (p. 352). Formula (4.2) is the local Whittaker
function of the induced representation: a double integral over `N_v` and the compact group
`°K_v` of a power of the modulus character `δ_(P,v)` at `b(g n w₀)`, the pairing
`⟨σ̃_v(k(g n w₀)) σ_v(k_v⁻¹) v, ṽ⟩` of the chosen vector `v`, acted on by `σ_v(k_v⁻¹)` and by
`σ̃_v` at the compact Iwasawa factor `k(g n w₀)`, with the chosen dual vector `ṽ`, the
Whittaker function `°w_v` of the inducing representation and the conjugate of the additive
character. Here (§2, pp. 177–178, PDF pages 8–9) `σ_v` is the finite-dimensional
representation of `°K_v` on the span of the `°K_v`-translates of `°w_v`, and `σ̃_v` is a fixed
finite-dimensional representation of `K_v` whose restriction to `P_v ∩ K_v` contains `σ_v`.
The domination by an intertwining integral is Shahidi's argument of 1981, p. 352, not part of
(4.2). The 1978 paper works with a simple group of type `G₂` split over `ℚ` and the maximal
parabolic subgroup of its §2 (§1, p. 173; §2, p. 176; PDF pages 4 and 7), and remarks (p. 173)
that its computations can be done for an arbitrary Chevalley group; the 1981 proof applies them
in its §5, where the group is a reductive group split over `ℚ` (§1.2, p. 300, PDF page 5).

The proof here follows the same comparison for the global two-block `GL` open-cell integral
rather than for its local components. The pointwise bound (step 1, through the slice and determinant modules)
dominates the integrand by a constant multiple of `Ω_e`, with `e = Re s + b ≥ 0`. The
convergence of the dominating integral is then proved directly for this product majorant, and
these estimates are internal to the formal proof, not taken from Shahidi: the lower integral of
`Ω_e` is reduced to the integral of the single Japanese-bracket weight `(1 + ‖x‖)^(-e)` over the
real vector space `ArchRow F D` of all archimedean coordinates together (finite for `e > d`),
times the Haar measure of the compact set of integral finite-adelic coordinates, and to the
products of the separate finite-place sums over `M(F_v)/M(𝒪_v)` (bounded uniformly for
`e > D + 1`). No convergence statement for (4.2) or for a local intertwining integral at a single
place is used.
