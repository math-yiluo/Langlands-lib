# Corrections compatible with a partial section

Author: Worker 60 (Task 7805). Module
`Langlands.GroupScheme.Trigonalizable.RelativeCorrection`, namespace
`Langlands.GroupScheme.LinearAdditiveExtension`.

The Library splits an extension `q : E ⟶ D(Λ)` whose kernel is a closed
subgroup `a` of `𝔾ₐ` in three steps (Milne 15.34(d),
`LinearAdditiveExtension`): an equivariant function, a crossed homomorphism
`c'`, a corrected crossed homomorphism `c''` with values in the range of `a`,
and then the section. This module adds a variant of the last two steps in
which a homomorphism `σ₁ : D(Λ₁) ⟶ E` is given in advance. The correction is
chosen to vanish on the image of `σ₁`, so that the resulting section `s`
satisfies `s ∘ q ∘ σ₁ = σ₁`.

## Notation

`k : Type u` is a field, `Λ` and `Λ₁` are additive commutative groups in
`Type u`, `D(Λ)` is `Diagonalizable.groupScheme (CommRingCat.of k) Λ`, and
`𝔾ₐ` is `VectorGroup.groupScheme (CommRingCat.of k) 1`. For a point `x` of
`𝔾ₐ` over `T`, `cd x` is its coordinate in `Γ(T, ⊤)`. `chi q χ g` is the value
of the character `χ` at `q(g)`. `E`, `q`, `a`, `χ` and `b` are as in the
Library's `exists_corrected`: `q` is flat, surjective and quasi-compact,
`a : kernel q ⟶ 𝔾ₐ`, and `b` is an action of `D(Λ)` on `kernel q` with the
linearity law `hlin` (it acts through the weight `χ`).

## Declarations

- `exists_section_vanishing`: if a crossed homomorphism `c : E ⟶ 𝔾ₐ` (with
  `hc₁`: `c(gh) = c(g) + χ(q g) c(h)`, and `hc₂`: `c` restricts to `a` on the
  kernel) has all values in the range of `a` (`hc₃`), then there is a
  homomorphic section `s` of `q` with `c(s(q(g))) = 0` for every point `g` of
  `E`. The proof is the Library's proof of `exists_section`
  (`LinearAdditiveExtension.Section`): `σ(g) = g · w(g)` with `w` built from
  `c`, which descends along `q`; the vanishing `c(σ(g)) = 0` is the identity
  proved there and is now also recorded in the conclusion.
- `exists_average_crossed`: let `e : D(Λ₁) ⟶ D(Λ)` be a morphism of schemes
  and `φ : D(Λ₁) ⟶ 𝔾ₐ` satisfy `φ(z z') = φ(z) + χ(e z) φ(z')` at all
  points. Then a constant `r` (a point of `𝔾ₐ` over the base) satisfies
  `r = φ(z) + χ(e z) r` at every point `z`, so `φ = r (1 - χ ∘ e)`. The
  constant is the average of `φ`, computed with the Library's
  `DiagonalizableAverage` (translation invariance, `average_mul`,
  `average_weightAction`), exactly as in the averaging step of
  `exists_corrected`.
- `exists_corrected_relative`: let `σ₁ : D(Λ₁) ⟶ E` be a homomorphism, `f`
  the closed polynomial of `a` and `N` its degree. Assume
  - `hrel₁`: if `f ≠ 0` and `χ(q σ₁ z)^N = 1` for all points `z`, then
    `χ(q σ₁ z) = 1` for all `z`;
  - `hrel₂`: if `f ≠ 0` and `χ(q σ₁ z) = 1` for all `z`, then every element
    of `k` is a value of `f`, or `χ^N = 1` on all of `D(Λ)`.

  Then every crossed homomorphism `c'` with `hc₁` and `hc₂` can be corrected
  to `c''` with `hc₁`, `hc₂`, all values in the range of `a`, and
  `c''(σ₁ z) = 0` for all points `z` of `D(Λ₁)`.

## Proof of `exists_corrected_relative`

The candidates are `c'_r = c' + r (χ ∘ q - 1)` for `r ∈ k`; each satisfies
`hc₁` and `hc₂`.

- Restricted along `σ₁`, `c'` is a crossed homomorphism of `D(Λ₁)` for the
  weight `χ ∘ q ∘ σ₁`. `exists_average_crossed` gives `m₁ ∈ k` with
  `c'(σ₁ z) = m₁ (1 - χ(q σ₁ z))`. So `c'_r` vanishes on the image of `σ₁`
  when `r = m₁`, or when `χ ∘ q ∘ σ₁ = 1`.
- As in the Library proof, `f ∘ c'` descends to `hD : D(Λ) ⟶ 𝔾ₐ`, a crossed
  homomorphism for `χ^N`, and averaging gives `m₀ ∈ k` with
  `f(c'_r(g)) = (f(r) - m₀) (χ(q g)^N - 1)`. So `c'_r` has values in the range
  of `a` when `f(r) = m₀`, or when `χ^N = 1`.
- Evaluating along `σ₁` gives `(f(m₁) - m₀) (1 - χ(q σ₁ z)^N) = 0`.

If `f = 0`, take `r = m₁`. If `f(m₁) = m₀`, take `r = m₁`. Otherwise
`f(m₁) - m₀` is a nonzero constant, so `χ(q σ₁ z)^N = 1` for all `z`. Then
`hrel₁` gives `χ ∘ q ∘ σ₁ = 1`, and `hrel₂` gives either a root `r` of
`f(r) = m₀` (and vanishing holds since `χ ∘ q ∘ σ₁ = 1`) or `χ^N = 1` (take
`r = m₁`).

## Provenance

Internal. It extends the published Library proofs in
`Langlands/GroupScheme/LinearAdditiveExtension/Correction.lean` and
`Section.lean`, which follow Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Theorem 15.34 and its proof (printed p.319). The requirement that the section
extend a given partial section is not in the source. It serves the proof of
case (b) of Milne 16.26 in
[`ExtensionSplitPerfectSmooth`](ExtensionSplitPerfectSmooth.md).
