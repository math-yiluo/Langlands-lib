# Uniform Harish-Chandra equations for the twists `φ_λ`

Module `Langlands.Global.AdelicInducedHarishChandraStatement`. It contains one statement,
`Langlands.Global.InducedHarishChandraEquationsStatement`, and no proof.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
  J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`): §8.3, Lemma 8.3 ("a result of
  Harish-Chandra") and the Remark after it, journal p.223.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995)
  (literature id `moeglin-waldspurger-1995-spectral-decomposition`). Lemma I.4.4(a) is on
  printed p.59. Its proof in I.4.5 is on printed pp.60–62, in the chapter file
  `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`.

Provenance: derived. BL state Lemma 8.3 for automorphic forms on `G(F) \ G(𝔸)` whose cuspidal
components along every standard parabolic lie in fixed finite-dimensional spaces, with
exponents in a family of parameters `Λ`. The statement here applies the same lemma to a
different family: the twists `φ_λ = φ · m_P^λ` of one automorphic form `φ` on the parabolic
quotient `X_P = U(𝔸) M(F) \ G(𝔸)`, as `λ` runs over `X^*(P) ⊗ ℂ`. Along a standard parabolic
`Q ⊆ P` the cuspidal components of `φ_λ` are those of `φ`, twisted by `λ`. So they lie in
the fixed finite-dimensional cuspidal spaces of `φ`, with exponents depending affinely on
`λ`, which is the situation of Lemma 8.3. The proof in MW I.4.5 carries over to `X_P`.
Its ingredients are: the finite-dimensional space of the cuspidal components; an
approximate identity `f`, smooth, compactly supported and bi-`K`-finite; the characteristic
polynomial of `δ(f)` on that space, whose coefficients depend holomorphically on the
parameter; and the vanishing criterion for automorphic forms on `X_P` whose cuspidal
components all vanish. The last one is BL (8.1), MW I.3.4. The Library states it as
`Langlands.Global.ParabolicCuspidalVanishingStatement`.

The intended use is BL's equations (8.2a) for the Eisenstein series. The Library module
`Langlands.Global.AdelicEisensteinHarishChandraEquations` derives them from this statement
by summing over `P(F) \ G(F)`, and so needs neither BL's Lemma 8.2 nor the constant-term
formula (6.18).

## Statement

`InducedHarishChandraEquationsStatement.{u}`. The setting is that of
`EisensteinAbsoluteConvergenceStatement`, with one more hypothesis,
`LocallyOfFiniteType G.X.hom`, which the convolution operator `rightConvolution` requires:

- `G` is a connected reductive group over a number field `F`, `p : P → G` a parabolic with
  unipotent radical `iU : U → P` and Levi `l : M → P`, presented by
  `r : ParabolicRootPresentation p l a` through the split component `a : A → M`;
- `K ≤ G(𝔸)` is a maximal compact subgroup with `P(𝔸) K = G(𝔸)` (`hK : IsIwasawaCompact p K`);
- `rho` is a closed matrix embedding;
- `φ` is an automorphic form on `U(𝔸) M(F) \ G(𝔸)`: `IsAutomorphicFunctionOn` for the
  subgroup `parabolicQuotientSubgroup F p iU l` and the archimedean part
  `K_∞ = K.comap (ofInfinite F G)` of `K`.

Then for all `n`, linear coordinates `e : ℂⁿ ≃ₗ[ℂ] X^*(P) ⊗ ℂ` and `s₀ ∈ ℂⁿ` there are:

- a number `m` and functions `h k : G(𝔸) → ℂ` (`k < m`), each
  - a smooth compactly supported test function (`IsAdelicTestFunction`, BL's
    `C_c^∞(G(𝔸))`),
  - right `K_∞`-finite (`IsInfiniteSubgroupFiniteFunction` for `K_∞`), and
  - left `K_∞`-finite (the same predicate for `g ↦ h k g⁻¹`, whose right translates are the
    left translates of `h k`);
- functions `b k`, `c : ℂⁿ → ℂ`, complex differentiable on all of `ℂⁿ`, with `c s₀ ≠ 0`,

such that for every `s ∈ ℂⁿ` and every `x ∈ G(𝔸)`

`∑_k b k s · (δ(h k) φ_{e s})(x) = c s · φ_{e s}(x)`.

Here `φ_λ = hK.parameterTwist φ λ`, that is, `φ_λ(g) = φ(g) exp⟨λ, H_P(g)⟩` with the Iwasawa
height `H_P` of `K`. The operator `δ(h) f (x) = ∫ h(g) f(x g) dg` is `rightConvolution` for
the Haar measure of `G(𝔸)`.

## Comparison with Bernstein–Lapid, Lemma 8.3

- BL use one bi-`K`-finite `h` and its convolution powers: `∑_{i=1}^d b_i(λ) δ(h)^i φ =
  b_0(λ) φ`. Here finitely many test functions appear with arbitrary entire coefficients.
  BL's form gives this one with `h k = h^{*k}`, `b k = b_k` and `c = b_0`, since
  `δ(h)^k = δ(h^{*k})`. Conversely, this form is all that BL's §8.4 uses.
- BL's `K`-finiteness is with respect to the whole `K`. Finiteness under the finite-adelic
  part of `K` follows from the bi-invariance under an open compact subgroup that comes with
  `IsAdelicTestFunction`. The statement therefore only asks for finiteness under `K_∞`. BL's
  Lemma 8.1 needs this bi-finiteness: if `c(λ) ≠ 0`, the single test function
  `c(λ)⁻¹ ∑_k b_k(λ) h_k` is bi-`K_∞`-finite and fixes `φ_λ`.
- BL's parameter `λ` lies in a finite sum of complex parameter spaces and the identity holds
  for all `λ`. Here `λ = e s` runs over `X^*(P) ⊗ ℂ` in linear coordinates, and the identity
  holds for every `s`, not only near `s₀`.
- The remark after BL's lemma, on choosing `h` with small support, is not included.
