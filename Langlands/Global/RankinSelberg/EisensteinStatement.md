# Analytic properties of the mirabolic Eisenstein series

This module states the analytic properties of the Eisenstein series `E(g, Φ; s, η)` of the
equal-rank global Rankin–Selberg integral. The source is J. W. Cogdell, *Analytic theory
of L-functions for GL_n* (2004), §2.3, printed p.209 (PDF p.212), registered as
`cogdell-2004-analytic-theory-gln`. Cogdell derives the properties from Poisson summation
and refers to H. Jacquet and J. A. Shalika, *On Euler products and the classification of
automorphic representations* (Amer. J. Math. 103, 1981), his reference [25], Section 4.
The objects are defined in `Langlands.Global.RankinSelberg.EqualIntegrals`; the
Schwartz–Bruhat space `schwartzBruhat` and the Fourier transform `fourierTransform` are
defined in `Langlands.Global.RankinSelberg.SchwartzBruhat`. All declarations are in the
namespace `Langlands.Global.RankinSelbergGlobal`. The character `η` is written `χ` in
Lean, because `η` is a reserved token under `open scoped CategoryTheory.MonObj`. The local
name for Cogdell's map `g ↦ g^ι` is `transposeInv`, because `ι` is also a notation under
that scope.

The two local instances `eisensteinSchemeAffine` and `eisensteinSchemeSmooth` repeat the
Library's facts that `GL_n` is affine and smooth, for the adelic points; they are `local`.

## The helper predicate

`HasAtMostSimplePolesIn f P` says that `f : ℂ → ℂ` is complex differentiable on the
complement of `P`, and that at each `p ∈ P` the function `(s - p) f(s)` is bounded on a
punctured disc around `p`. When `P` is finite, as it is here, the complement of `P` is open
and connected. Then by Riemann's removable singularity theorem `(s - p) f(s)` extends
holomorphically across `p`. So `f` is meromorphic on `ℂ`, holomorphic off `P`, and has at
most simple poles at the points of `P`. The value `f(p)` itself is irrelevant. This is
how the statement expresses "meromorphic continuation with at most simple poles in `P`".

## The statement

`EisensteinStatement` says the following. Let `F` be a number field, in an arbitrary
universe `u`, with the Library's standing hypothesis `CompactSpace (AdeleQuotient F)`. Let
`n = r + 1`. Let `ψ` be a continuous nontrivial unitary character of `𝔸` trivial on `F`
(the Library's `IsStandardAdditiveCharacter`), `χ` a continuous character of
`F^× \ 𝔸^×`, and `Φ ∈ S(𝔸^n)`. Write `Φ̂ = fourierTransform F n ψ Φ` and
`g^ι = ᵗg⁻¹`. Then there are a real `σ₀` and functions `E, Ê : GL_n(𝔸) → ℂ → ℂ` such that:

1. **Convergence.** For every `g` and every `s` with `Re s > σ₀`:
   * the integrand `a ↦ Φ(a e_n g) |a|^(ns) χ(a)` of the section `F(g, Φ; s, χ)` is
     integrable for `d^×a = ideleMeasure F`, and so is the integrand of
     `F(g, Φ̂; s, χ⁻¹)`;
   * the series `Σ_(γ ∈ P'_n(F) \ GL_n(F)) |F(γ g, Φ; s, χ)|` converges, and so does the
     series for `(Φ̂, χ⁻¹)`. In Lean the sum runs over `LeftCosetSpace (eisensteinParabolic
     F r)` at the chosen representatives `q.out`, exactly as in `eisensteinSeries`;
   * `E(g, s) = E(g, Φ; s, χ)` and `Ê(g, s) = E(g, Φ̂; s, χ⁻¹)`, the series of
     `eisensteinSeries`.
2. **Continuation.** For every `g`, `E(g, ·)` has at most simple poles in `P(χ)` and
   `Ê(g, ·)` has at most simple poles in `P(χ⁻¹)`, in the sense of
   `HasAtMostSimplePolesIn`. `P(χ) = equalPoleSet F n χ` is `{-w/n, 1 - w/n}` if
   `χ = |·|^w`, and empty otherwise.
3. **Vertical strips.** For every compact set `K ⊆ GL_n(𝔸)`, all reals `a ≤ b` and every
   `δ > 0`, `E(g, s)` is bounded for `g ∈ K` and `a ≤ Re s ≤ b` at distance at least `δ`
   from `P(χ)`.
4. **Functional equation.** For every `g` and every `s ∉ P(χ)`,
   `E(g, s) = Ê(g^ι, 1 - s)`, that is, `E(g, Φ; s, η) = E(g^ι, Φ̂; 1 - s, η⁻¹)`.

`P(χ⁻¹) = 1 - P(χ)`, since `χ⁻¹ = |·|^(-w)` when `χ = |·|^w`. So `1 - s ∉ P(χ⁻¹)` in
clause 4.

The continuations `E` and `Ê` are existentially quantified, but they are not arbitrary.
Each `E(g, ·)` agrees with the series on the half-plane `Re s > σ₀` and is holomorphic on
the connected open set `ℂ \ P(χ)`. So it is the unique analytic continuation there, and
clauses 3 and 4 are statements about the series itself. Every convergence and
integrability claim is in the conclusion.

## Comparison with the source

Cogdell (p.209) states: "The Eisenstein series `E(g, Φ; s, η)` has a meromorphic
continuation to all of `ℂ` with at most simple poles at `s = -iσ, 1 - iσ` when `η` is
unramified of the form `η(a) = |a|^(inσ)`. As a function of `g` it is smooth of moderate
growth, and as a function of `s` it is bounded in vertical strips (away from the possible
poles), uniformly for `g` in compact sets. Moreover, we have the functional equation
`E(g, Φ; s, η) = E(g^ι, Φ̂; 1 - s, η⁻¹)`, where `g^ι = ᵗg⁻¹`." On p.208 he states absolute
convergence for `Re(s) > 1`.

* **Convergence region.** Cogdell takes `η` unitary and gets absolute convergence for
  `Re s > 1`. Here `χ` is any continuous character. Every such character is
  `χ_0 |·|^(σ')` with `χ_0` unitary and `σ'` real, so the series converges for
  `Re s > 1 - σ'/n`. The statement only asserts some right half-plane `Re s > σ₀`.
* **Poles.** For unitary `η`, Cogdell's poles `-iσ, 1 - iσ` are `-w/n, 1 - w/n` with
  `w = inσ`. For a general `χ = |·|^w`, `w ∈ ℂ`, the Poisson summation formula on p.209
  gives boundary terms `Φ(0) ∫_(|a| ≤ 1) |a|^(ns + w) d^×a` and
  `Φ̂(0) ∫_(|a| ≤ 1) |a|^(ns + w - n) d^×a`. These have their poles at `s = -w/n` and
  `s = 1 - w/n`. If `χ` is not of the form `|·|^w`, its integral over `F^× \ 𝔸^1`
  vanishes, so there is no pole.
* **Omitted.** Smoothness and moderate growth in `g` are not stated. The source objective
  does not ask for them, and the analytic statement for `I(s; φ, φ', Φ)` is stated
  directly. The residues (the constant `c` and `δ(s)` on p.209) are not stated either.
* **The Fourier transform.** `Φ̂` is taken for the covolume-one Haar measure on `𝔸^n`. This
  is the self-dual measure; see `Langlands.Global.RankinSelberg.SchwartzBruhat`. With this
  measure Poisson summation has no constant, and the functional equation holds as stated.
  It holds for every `ψ` of the stated kind.
* **The measure `d^×a`.** The section uses `ideleMeasure F`. A different normalization would
  multiply `E` and `Ê` by the same constant and change nothing in the statement.
