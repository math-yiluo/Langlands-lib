# Forms with only negative maximal cuspidal exponents on Levi Siegel regions

Module `Langlands.Global.AdelicCuspidalExponentRegionBound`. It states and proves
`Langlands.Global.StandardParabolicFamily.CuspidalExponentRegionBoundStatement` (theorem
`cuspidalExponentRegionBound`). An automorphic function `f` on `U_R(𝔸) M_R(F) \ G(𝔸)` is bounded
on Siegel regions of the Levi `M_R`, provided that for every simple root `α ∈ R` the constant term
of `f` along the maximal parabolic `Q_α = R \ {α}` of `M_R` is a sum of cuspidal components whose
nonzero members have unnormalized exponents `μ` with `⟨Re μ, β^∨⟩ < 0`, where `R = Q_α ∪ {β}`.

This is the boundedness that Bernstein–Lapid derive in §6.4 from Mœglin–Waldspurger I.4.1, on a
Siegel region of `M_R` and for forms whose cuspidal exponents along proper parabolics all sit on
the maximal parabolics of `M_R`.

## Auxiliary lemmas

- `adelicIteratedDirectionalValue_sub_of_smoothSlices`: a derivative word of `f − g` is the difference of the
  derivative words of `f` and `g`, when both are smooth on the archimedean slices. On a slice the
  derivative words are linear maps on the smooth functions of `G(F_∞)`.
- `exists_derivativeGrowth_of_automorphicOn`: the derivative words of an automorphic function on
  `U_P(𝔸) M_P(F) \ G(𝔸)` are bounded by `C_s ht(x)^e`, with one exponent `e ≥ 0` for all words
  `s`. This is the published `exists_uniformGrowth_functionInfiniteSlices`, rewritten with
  `plotSmoothEnvelopingAction_directionalWord_slice`. It needs `N > 0` and a maximal compact
  subgroup `Kinf` of `G(F_∞)`.
- `IsAutomorphicOn.regularData`: an automorphic function on `U_P(𝔸) M_P(F) \ G(𝔸)` is continuous
  and smooth on the archimedean slices. It is left invariant under `P_0(F)` (published
  `rationalImage_le_parabolicQuotientSubgroup_of_le`) and under `U_P(𝔸)`, and right invariant
  under an open subgroup of `G(𝔸_f)`.
- `constantTerm_sub_of_le`: for `Q ⊆ P` and `Q ⊆ P'`, let `f₁` and `f₂` be continuous and left
  invariant under `U_P(𝔸) M_P(F)` and `U_{P'}(𝔸) M_{P'}(F)` respectively. Then
  `C_Q(f₁ − f₂) = C_Q f₁ − C_Q f₂`. Both integrands are integrable on the compact quotient
  `U_Q(F) \ U_Q(𝔸)` (published `integrable_constantTermIntegrand_of_le`).
- `relativeCharacterDecay_pow_eq_exp`: `(|α(a)|^{-1/[F:ℚ]})^n = exp(−n log|α(a)| / [F:ℚ])`.

## The statement

`CuspidalExponentRegionBoundStatement 𝓕 hG rho` assumes `N > 0` and that `rho` is a closed
embedding. Let `Kinf` be a maximal compact subgroup of `G(F_∞)`, `R` a standard index and `f` an
automorphic function on `U_R(𝔸) M_R(F) \ G(𝔸)` (`IsAutomorphicOn`). Let `s` and `c` assign to
every standard index `Q` a finite set of parameters and functions. Assume, for every `α ∈ R`, with
`Q_α = removeSimpleRoot R α`:

- `C_{Q_α} f = ∑_{μ ∈ s(Q_α)} c(Q_α, μ)` is an exponent decomposition (`IsExponentDecomposition`):
  every `c(Q_α, μ)` is automorphic on `U_{Q_α}(𝔸) M_{Q_α}(F) \ G(𝔸)`, cuspidal along `Q_α` and
  has unnormalized exponent `μ`;
- if `c(Q_α, μ) ≠ 0`, there is a relative root `β ∉ Q_α` with `Q_α ∪ {β} = R` and
  `⟨Re μ, β^∨⟩ < 0`.

Let `Φ` be a set of real linear forms on `𝔞_0`, contained in `corootAnnihilator R`, such that `Φ`
and the simple roots of `R` span `𝔞_0^*`. Fix a real number `b > 0` (in Lean a unit of `ℝ≥0`), a
real number `B ≥ 0`, compact sets `Ω ⊆ P_0(𝔸)` and `K` of `G(𝔸)`, and a compact set `Y_f` of
finite adelic points. Then there is `C ≥ 0` with `|f(p a k)| ≤ C`. Here `p ∈ Ω`, `k ∈ K`, and the
finite part of `p a k` lies in `Y_f`. The point `a` is a positive torus point with logarithm `H`.
The normalized adelic norms of the simple roots of `R` at `a` are bounded below by `b`:
`|γ(a)|_𝔸 ≥ b` for `γ ∈ R` (`normCharacter`). The forms of `Φ` are bounded at `H`:
`|φ(H)| ≤ B` for `φ ∈ Φ`.

No condition is imposed on the simple roots outside `R`.

## The proof (`cuspidalExponentRegionBound`)

For `α ∈ R` the constant term `C_{Q_α} f` is automorphic on `U_{Q_α}(𝔸) M_{Q_α}(F) \ G(𝔸)`
(published `constantTermAutomorphy`). Let `e_f` and `e_α` be common growth exponents for the
derivative words of `f` and of `C_{Q_α} f`, and `e = e_f + ∑_α e_α`.

**The remainders.** Put `g_α = f − C_{Q_α} f`. It is continuous and smooth on the archimedean
slices. It is left invariant under `P_0(F)`, and under `U_R(𝔸)`, since `U_R ⊆ U_{Q_α}` (published
`radical_le_of_le`). It is right invariant under `L_f ∩ L_α`, the intersection of open levels of
`f` and of `C_{Q_α} f`. Its constant term along `Q_α` is `C_{Q_α} f − C_{Q_α}(C_{Q_α} f) = 0`, by
`constantTerm_sub_of_le` and because `C_{Q_α} f` is invariant under `U_{Q_α}(𝔸)` (published
`constantTerm_eq_self_of_automorphicOn`). Its derivative words are bounded by `C ht(x)^e`.

**The components.** Fix `α ∈ R` and `μ ∈ s(Q_α)` with `c(Q_α, μ) ≠ 0`, and let `β` be given by
the hypothesis. By `IsAutomorphicOn.regularData` and `exists_derivativeGrowth_of_automorphicOn`,
the function `c(Q_α, μ)` satisfies the hypotheses of `cuspidalExponentLineBound` (module
`Langlands.Global.AdelicCuspidalExponentLineBound`) for `Q_α ⊆ R = Q_α ∪ {β}`. Its cuspidality is
`C_{Q'} c(Q_α, μ) = 0` for `Q' = removeSimpleRoot Q_α γ < Q_α` (published `removeSimpleRoot_lt`).
So `|c(Q_α, μ)|` is bounded on the region by a constant `C_{α,μ}`, and
`|C_{Q_α} f| ≤ S_α = ∑_μ C_{α,μ}` there.

**The decay.** The lemma `exists_regionHeight_bound` in `Langlands.Global.AdelicShiftedMaximalDecay`
gives `C₀ ≥ 1` and `r ≥ 0` with
`ht(a) ≤ A₀ e^{r t}`, where `A₀ = C₀ e^{r max(B, −log b)}`, whenever `log|γ(a)| ≤ t` for all
`γ ∈ R`, with `t ≥ 0`. Choose `n` with `n/[F:ℚ] ≥ r e`. By `shiftedMaximalDecay` (module
`Langlands.Global.AdelicShiftedMaximalDecay`) for `J = R` and the root `α`, applied to `g_α` with
words of length `n`, `|g_α(p a k)| ≤ C_α |α(a)|^{-n/[F:ℚ]} W_α ht(a)^e`.

**The cases.** Fix a point `p a k` of the region. Among the values `0` and `log|γ(a)|`, `γ ∈ R`,
choose a largest one, and let `t ≥ 0` be its value.

- If the chosen value is `0` (this is the only choice when `R` is empty), then `log|γ(a)| ≤ 0` for
  all `γ ∈ R`, so `ht(a) ≤ A₀`. The lemma `exists_compact_factors_height_bound` in
  `Langlands.Global.AdelicRelativeCuspidalRapidDecay` gives `ht(p a k) ≤ E₀ ht(a)`, and the growth of `f` gives `|f(p a k)| ≤ C_f (E₀ A₀)^{e_f}`.
- If the chosen value is `t = log|α(a)|` for a root `α ∈ R`, then
  `|α(a)|^{-n/[F:ℚ]} ht(a)^e ≤ A₀^e e^{(r e − n/[F:ℚ]) t} ≤ A₀^e`, so
  `|g_α(p a k)| ≤ C_α W_α A₀^e`. Hence
  `|f(p a k)| ≤ |g_α(p a k)| + |C_{Q_α} f(p a k)| ≤ C_α W_α A₀^e + S_α`.

The constant is `C_f (E₀ A₀)^{e_f} + ∑_{α ∈ R} (C_α W_α A₀^e + S_α)`.

## Sources and provenance

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.10 (pp. 30–33), the decay
  of `f − C_P f` along a maximal parabolic, and I.4.1 (p. 49), the bound of an automorphic form
  on a Siegel set by `∑ m_{P_0}(g)^{Re π + ρ_P} (1 + ‖log m_P(g)‖)^{deg}` over its cuspidal data.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series* (2024),
  registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: §6.4 (p. 204), where
  I.4.1 is applied to forms whose cuspidal exponents along proper parabolics are attached to
  maximal parabolics and pair negatively with the coroot.

The statement is derived. It is the bound on Siegel regions of `M_R` that Bernstein–Lapid take
from I.4.1 for these forms. The proof does not follow the proof of I.4.1. It covers the Siegel
region by the parts where one simple root of `R` is largest, and on each part compares `f` with
its constant term along the corresponding maximal parabolic of `M_R` by the decay of I.2.10.
`AdelicCuspidalExponentLineBound` bounds the components of that constant term.
