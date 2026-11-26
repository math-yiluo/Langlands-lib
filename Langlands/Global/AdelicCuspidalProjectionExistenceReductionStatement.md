# Reduction of the existence of cuspidal projections

Module `Langlands.Global.AdelicCuspidalProjectionExistenceReductionStatement` states the
proposition `Langlands.Global.CuspidalProjectionExistenceReductionStatement` (universe `u`) and
proves nothing.

## Statement

`CuspidalProjectionExistenceReductionStatement` is the implication

```
LeviCuspFormPairingMajorantStatement → ParabolicCuspidalVanishingStatement →
  ParabolicReproducingKernelStatement → ContinuousCuspidalProjectionExistenceStatement →
    CuspidalProjectionExistenceStatement
```

with every proposition at universe `u`. The premises and the conclusion are:

- `LeviCuspFormPairingMajorantStatement` (module `Langlands.Global.AdelicLeviCuspFormMajorantStatement`):
  for every cusp form `t` on a standard Levi `M_J(F) \ M_J(𝔸)`, every `g ∈ G(𝔸)` and every real
  `R`, the function `m ↦ ‖ι(m) g‖^R |t(m)|` on `M_J(F) \ M_J(𝔸)^1`, evaluated at suitable
  representatives, has an integrable majorant (`HasLeviPairingMajorant`).
- `ParabolicCuspidalVanishingStatement` (module `Langlands.Global.AdelicCuspidalAnnihilator`): a
  continuous function of moderate growth on `U_P(𝔸) M_P(F) \ G(𝔸)` whose constant terms along all
  standard `Q ≤ P` lie in the fibrewise cuspidal annihilator vanishes.
- `ParabolicReproducingKernelStatement` (module
  `Langlands.Global.AdelicParabolicReproducingKernelStatement`): every automorphic function `φ` on
  `U_Q(𝔸) M_Q(F) \ G(𝔸)` satisfies `rightConvolution F G α φ = φ` for a smooth compactly supported
  test function `α` with finite-dimensional span of left `K_∞`-translates.
- `ContinuousCuspidalProjectionExistenceStatement` (module
  `Langlands.Global.AdelicContinuousCuspidalProjectionStatement`): every automorphic `φ` on
  `U_Q(𝔸) M_Q(F) \ G(𝔸)` has a continuous cuspidal projection, a continuous function of moderate
  growth on the same quotient, cuspidal along `Q`, with the same absolutely convergent norm-one
  Levi pairings as `φ` against every Levi cusp form at every point.
- `CuspidalProjectionExistenceStatement` (module
  `Langlands.Global.AdelicCuspidalProjectionExistenceStatement`): every such `φ` has a cuspidal
  projection in the sense of `StandardParabolicFamily.IsCuspidalProjection`, which is moreover
  automorphic.

## Mathematical content

The implication says that a continuous cuspidal projection can be made automorphic. Fix the
data of the target, an automorphic `φ` on `U_Q(𝔸) M_Q(F) \ G(𝔸)` and a continuous cuspidal
projection `ψ₀` of `φ` given by `ContinuousCuspidalProjectionExistenceStatement`. The argument
distinguishes the size `N` of the matrix embedding, since the target quantifies over every
`N : ℕ` while `ParabolicCuspidalVanishingStatement` assumes `0 < N`.

**Size zero.** The closed embedding into `GL_0(𝔸)`, a one-point group, makes `G(𝔸)` a single
point. Every function on it is then automorphic: it is continuous and constant, hence smooth,
fixed by every open subgroup, `K_∞`-finite, and annihilated by an ideal of finite codimension of
the centre of the enveloping algebra. So `ψ₀` itself is the required projection; its cuspidality
and its pairing identities are part of the continuous premise.

**Positive size.** Let `α` be a reproducing kernel of `φ`. The candidate is the right
convolution `ψ = ψ₀ * α`, `ψ(g) = ∫ α(a) ψ₀(g a) da`.

- Right convolution by a smooth compactly supported kernel makes `ψ` smooth with a finite level,
  preserves the left invariance, the moderate growth and the cuspidality along `Q`, and the left
  `K_∞`-finiteness of `α` makes `ψ` right `K_∞`-finite.
- The majorants of the Levi cusp forms justify Fubini's theorem for the pairings:
  `(ψ(·g), t) = ∫ α(a) (ψ₀(·ga), t) da = ∫ α(a) (φ(·ga), t) da = ((φ * α)(·g), t) = (φ(·g), t)`.
- For the centre `𝔷` of the enveloping algebra, an element `z` acting on `ψ₀ * α` is right
  convolution `ψ₀ * α_z` with a test kernel `α_z` independent of the convolved function. If `z`
  annihilates `φ`, then `φ * α_z = z (φ * α) = z φ = 0`, so `ψ₀ * α_z` is a continuous cuspidal
  function of moderate growth whose Levi pairings all vanish. Its constant term along `Q` is
  itself, and its constant terms along the smaller standard parabolics vanish by cuspidality.
  The vanishing criterion `ParabolicCuspidalVanishingStatement` applies, since `N > 0` and the
  Iwasawa decomposition `P_R(𝔸) K = G(𝔸)` holds for every standard `R` because `P_R` contains
  the minimal parabolic `P_0`. It gives `ψ₀ * α_z = 0`; hence the annihilator ideal of `φ` in
  `𝔷` annihilates `ψ`.

The cuspidal projection of Mœglin–Waldspurger I.2.18 (pp. 39–40) is constructed automorphic
directly, for a fixed central character, by duality between finite-dimensional spaces of cusp
forms; Bernstein–Lapid (6.8) characterizes it by the fibrewise pairings used here. The
convolution argument above is different: it is a fibrewise adaptation of the proof of the
converse in the Lemma of Mœglin–Waldspurger I.3.5 (p. 48). There a function of moderate growth
whose cuspidal components are automorphic is convolved with a kernel from I.2.17 reproducing
those components; the vanishing criterion I.3.4 shows that the convolution does not change the
function, and that an ideal of finite codimension of `𝔷` annihilates it. Here the pairings are
those of Bernstein–Lapid (6.8), and the zero test is the Library's vanishing criterion
`ParabolicCuspidalVanishingStatement` (Mœglin–Waldspurger I.3.4; Bernstein–Lapid (8.1)). The
implication is internal to the Library and records how the remaining existence assertion,
`ContinuousCuspidalProjectionExistenceStatement`, combines with the three other premises.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), §6.2, p. 202 (the cuspidal projection and (6.8)), and (8.1), p. 221.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.17,
  Lemma, p. 38; I.2.18, pp. 39–40; I.3.4, pp. 45–46; I.3.5, pp. 47–48.
