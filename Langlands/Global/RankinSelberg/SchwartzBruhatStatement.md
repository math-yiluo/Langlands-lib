# The two descriptions of `S(𝔸^n)` and Fourier inversion

`SchwartzBruhatStatement` is a Prop-valued statement about the objects of
`Langlands.Global.RankinSelberg.SchwartzBruhat`. It records the basic facts about the
adelic Schwartz–Bruhat space `S(𝔸^n)` that the equal-rank Rankin–Selberg theory of
J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.3, printed
pp.208–209 (PDF pp.211–212), registered as `cogdell-2004-analytic-theory-gln`, uses
without comment. The statement is not proved here.

## The statement

For every number field `F : Type u` with `CompactSpace (AdeleQuotient F)` and every
`n : ℕ`:

1. `schwartzBruhat F n = restrictedSchwartzBruhat F n`. The span of the pure tensors
   `Φ_∞(x_∞) Φ_f(x_f)` equals the span of the restricted pure tensors
   `Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)`.
2. For every additive character `ψ` with `IsStandardAdditiveCharacter F ψ` (continuous,
   nontrivial, trivial on `F`, of absolute value one; the Library's predicate from
   `Langlands.Global.RankinSelberg.UnequalAnalyticStatement`) and every
   `Φ ∈ schwartzBruhat F n`:
   * for every `x`, the integrand `y ↦ Φ(y) ψ(y ᵗx)` of the Fourier transform is
     integrable for `rectangleMeasure F 1 n`;
   * `fourierTransform F n ψ Φ ∈ schwartzBruhat F n`;
   * Fourier inversion holds: `Φ̂̂(x) = Φ(-x)` for every `x`.

The hypothesis `CompactSpace (AdeleQuotient F)` is the Library's standing hypothesis for
global integrals. It makes the covolume-one normalization of `rectangleMeasure` a
genuine Haar normalization (see `Langlands.Global.RankinSelberg.WhittakerIntegrals`).
It holds for every number field.

## Sources

* Clause 1 is the restricted tensor product description of the space defined by
  J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  registered as `getz-hahn-2024-automorphic-representations`, §C.3, printed p.553
  (PDF p.558): `S(W(𝔸_F)) := S(W(F_∞)) ⊗ C_c^∞(W(𝔸_F^∞))`. The proof of Lemma C.3.1,
  printed p.554 (PDF p.559), uses the factorization `f = f_S 1_((𝒪^S)^r)` for `S` large
  enough. The equality holds because `C_c^∞(𝔸_f^n)` is spanned by characteristic
  functions of the compact open sets `a + ∏_v ϖ_v^(k_v) 𝒪_v^n` with `k_v = 0` for almost
  all `v`, each of which is a restricted pure tensor. Conversely every finite part
  `∏_(v ∈ S) Φ_v ⊗ 1_((𝒪^S)^n)` is locally constant with compact support on `𝔸_f^n`.
* Clause 2 is Getz–Hahn Lemma C.3.1, printed p.554 (the Fourier transform maps
  `S(W(𝔸_F))` to itself), together with the Fourier inversion formula (C.6), printed
  p.554, for the self-dual measure. Getz–Hahn use the pairing
  `⟨x, y⟩ = ∑_i x_i y_i` (proof of Lemma C.3.1), which is the pairing `y ᵗx` of Cogdell's
  Fourier transform (printed p.209).
* The measure: `rectangleMeasure F 1 n` is the Haar measure on `𝔸^n` with
  `F^n \ 𝔸^n` of volume one. The Markdown of
  `Langlands.Global.RankinSelberg.SchwartzBruhat` explains, from J. T. Tate,
  *Fourier analysis in number fields and Hecke's zeta-functions* (1967), registered as
  `tate-1967-thesis`, Theorems 4.1.1–4.1.3, printed pp.328–331 (PDF pp.173–174), why this
  is the self-dual measure for every nontrivial character of `F \ 𝔸`. Fourier inversion
  in clause 2 therefore holds with no constant. With another Haar measure it would fail
  by a positive factor, so clause 2 also pins down the measure normalization.

## Notes on the formalization

* Integrability is stated in the conclusion, not assumed. Lean's `∫` is total, so
  without this clause the Fourier transform of a non-integrable function would be `0`.
* The statement quantifies over all characters satisfying the Library's
  `IsStandardAdditiveCharacter`, not only the standard character `ψ_F` of Getz–Hahn
  (C.1). The facts hold for every nontrivial character of `F \ 𝔸`, by the
  measure-independence argument above.
* No topology on `S(𝔸^n)` and no continuity of the Fourier transform is stated; the
  global Rankin–Selberg theory does not use them.
