# A common growth space for regular Eisenstein series

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): §8.4, proof of Proposition 8.4,
pp.223–224, and §8.6, Corollary, p.226. There the Eisenstein series at sufficiently regular `λ`
is a solution of `Ξ_fnl(λ)` in the union of the growth spaces. To use a single Fréchet space
`𝔉^R_L` on a bounded set of parameters, one needs a common level `L` and a common exponent `R`.

The module **states** a proposition; nothing is proved here. It isolates this growth
assertion, which the paired Markdown of `AdelicEisensteinSystemDominationStatement` lists under
"Fréchet form".

## The statement `Langlands.Global.EisensteinCommonGrowthStatement`

The hypotheses are exactly those of `EisensteinSystemDominationStatement`: `G` connected
reductive over a number field `F`, a parabolic `p : P → G` with unipotent radical `iU`, Levi
`l` and split component `a` presented by `r`, a maximal compact `K` with `P(𝔸)K = G(𝔸)`
(`hK : IsIwasawaCompact p K`), a closed matrix embedding `rho`, and an automorphic form `φ`
on `U(𝔸)M(F) \ G(𝔸)`.

Conclusion: there is `R₀` such that for every `n`, every complex linear coordinate system
`e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every bounded set `W ⊆ ℂⁿ` there are a compact open subgroup
`L ≤ G(𝔸_f)` and a real `R₁` with the following property. For every `R ≥ R₁` and every
`s ∈ W` with `e s` `R₀`-regular (`r.IsRegularParameter hA hT R₀`), some `v ∈ 𝔉^R_L` (the
Library's `UniformGrowthFrechetSpace`: right `L`-invariant smooth functions on
`G(F) \ G(𝔸)` all of whose derivatives are bounded by multiples of `‖g‖^R`) has underlying
function `E(φ, e s)` (`hK.eisensteinSeries φ (e s)`).

`W` is an arbitrary bounded set; it need not be open. Only membership is asserted: the
constants in the growth bounds may depend on `s`; only the exponent `R` is uniform.

## Why it is true (not formalized here)

- **Level.** `φ` is right invariant under an open subgroup `L₀` of `G(𝔸_f)` (smoothness), and
  the Iwasawa height `H_P` is right invariant under `K`. So `φ_λ` and hence `E(φ, λ)` are right
  invariant under the compact open subgroup `L₀ ∩ K_f`, for every `λ`.
- **Exponent.** Choose `R₀` so that the `R₀`-regular parameters lie in the region of
  absolute convergence with a margin (`AdelicEisensteinConvergenceStatement.md` explains the
  Library's chamber). Then the regular parameters with `e s` in a bounded set have real parts
  in a compact subset of that region. There, `E(φ, λ)` is majorized by a convergent series of
  positive terms depending only on `Re λ`, as in the proof of Mœglin–Waldspurger,
  *Spectral decomposition and Eisenstein series*, Proposition II.1.5, pp.85–87. These
  majorants have moderate growth with an exponent bounded on that compact set. A derivative
  `R(X) E(φ, λ)` (`X` in the enveloping algebra) is the Eisenstein series of `R(X) φ_λ`, a
  finite combination of sections of the same kind. So one exponent `R₁` serves for all
  regular `s ∈ W` and all derivatives.
- **Alternative route.** The paired Markdown of `AdelicEisensteinSystemDominationStatement`
  obtains the exponent from the growth estimates of BL §§7.4–7.7 for solutions of `Ξ_main`.

## Use

This is one premise of the planned reduction proving `EisensteinSystemDominationStatement`. It
supplies the level `L` and the exponent `R₁` of that statement. It also places the regular
Eisenstein series in `𝔉^R_L`, which is needed for the existence half of the uniqueness clause.
