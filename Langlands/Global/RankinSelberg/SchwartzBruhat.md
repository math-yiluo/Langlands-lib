# The adelic Schwartz–Bruhat space `S(𝔸^n)` and its Fourier transform

This module defines the space of Schwartz–Bruhat functions on adelic row vectors and
their Fourier transform. These are the test functions `Φ` of the equal-rank global
Rankin–Selberg integral `I(s; φ, φ', Φ)` in J. W. Cogdell, *Analytic theory of
L-functions for GL_n* (2004), §2.3, printed pp.208–209 (PDF pp.211–212), registered as
`cogdell-2004-analytic-theory-gln`. Cogdell does not define the space; he writes
`S(𝔸^n)` for "the Schwartz–Bruhat functions on `𝔸^n`" (p.208). The Library had no
adelic Schwartz–Bruhat space on `𝔸^n`. The module
`Langlands.Global.Hecke.AdelicPoisson` only treats functions of one adelic variable
built for Hecke characters. So the space is defined here.

All declarations are concrete. The module asserts no property of these objects. That the
two spaces below coincide and that the Fourier transform preserves them are the
separate statement module `Langlands.Global.RankinSelberg.SchwartzBruhatStatement`.

`F` is a number field and `n` a natural number. All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal`.

## Row vectors and their coordinates

* `RowVector F n` is `Matrix (Fin 1) (Fin n) (Adeles F)`, the space `𝔸^n = M_(1,n)(𝔸)`
  of adelic row vectors. Cogdell writes `e_n g` and `y ᵗx` for row vectors (p.208,
  p.209), and the Library's matrix group acts on row vectors from the right. So the row
  convention is used.
* `archimedeanCoordinates F n x` is the vector `x_∞ ∈ (ℝ^(r₁) × ℂ^(r₂))^n` of archimedean
  coordinates. For each `j`, it applies Mathlib's ring isomorphism
  `InfiniteAdeleRing.ringEquiv_mixedSpace` to the infinite component of the entry
  `x 0 j`. This isomorphism identifies `F_∞ = ∏_(w | ∞) F_w` with the mixed space
  `mixedEmbedding.mixedSpace F = ℝ^(r₁) × ℂ^(r₂)`. It is a homeomorphism. The Library
  uses this fact in `Langlands.Global.ArchimedeanGL`.
* `finiteCoordinates F n x` is the vector `x_f ∈ (𝔸_f)^n` of finite components.
* `localCoordinates F n v x` is the vector `x_v ∈ F_v^n` of components at a finite place
  `v`. It applies the Library's `finiteProjection F v` to each entry.
* `integralOutside F n S` is the set of row vectors with `x_v ∈ 𝒪_v^n` at every finite
  place `v ∉ S`. Here `S` is a finite set of finite places and `𝒪_v` is
  `v.adicCompletionIntegers F`.

## The Schwartz–Bruhat space

The definition follows J. R. Getz and H. Hahn, *An Introduction to Automorphic
Representations* (2024), registered as `getz-hahn-2024-automorphic-representations`,
§C.3, printed p.553 (PDF p.558). For a finite-dimensional `F`-vector space `W` they set

`S(W(𝔸_F)) := S(W(F_∞)) ⊗_ℂ C_c^∞(W(𝔸_F^∞))`,

where `S(W(F_∞))` is the usual Schwartz space of the real vector space `W(F_∞)` and
`C_c^∞` means locally constant with compact support (§C.2, p.553). Here `W = F^n`.

* `IsPureSchwartzBruhat F n Φ` says that `Φ(x) = Φ_∞(x_∞) Φ_f(x_f)` for all `x`. Here
  `Φ_∞` is a Schwartz function on `(ℝ^(r₁) × ℂ^(r₂))^n`, that is, a term of Mathlib's
  `SchwartzMap`, and `Φ_f : (𝔸_f)^n → ℂ` is locally constant with compact support.
  Mathlib's `SchwartzMap` uses the norm of the real normed space
  `Fin n → mixedSpace F`. Any two norms on a finite-dimensional real space are
  equivalent, so this is the usual Schwartz space of `F_∞^n`.
* `schwartzBruhat F n` is the complex span of these pure tensors, a submodule of the
  functions `𝔸^n → ℂ`. The algebraic tensor product of Getz–Hahn maps onto this span by
  `Φ_∞ ⊗ Φ_f ↦ (x ↦ Φ_∞(x_∞) Φ_f(x_f))`. The space of functions is the one used in
  practice, so the span is taken directly.

The "restricted tensor product" description of the same space is also defined, because
the source objective allows either description provided their equivalence is stated.

* `IsRestrictedPureSchwartzBruhat F n Φ` says that for some finite set `S` of finite
  places, some Schwartz function `Φ_∞` and some locally constant compactly supported
  functions `Φ_v` on `F_v^n` for `v ∈ S`,
  `Φ(x) = Φ_∞(x_∞) ∏_(v ∈ S) Φ_v(x_v)` when `x_v ∈ 𝒪_v^n` for every finite `v ∉ S`, and
  `Φ(x) = 0` otherwise. That is,
  `Φ = Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)`. The functions `Φ_v` for `v ∉ S` are
  part of the data but are not used.
* `restrictedSchwartzBruhat F n` is the complex span of these restricted pure tensors.
  This is the restricted tensor product `S(F_∞^n) ⊗ ⊗'_v S(F_v^n)` with respect to the
  vectors `1_(𝒪_v^n)` (compare the proof of Getz–Hahn Lemma C.3.1, p.554, which writes
  `f = f_S 1_((𝒪^S)^r)`).

## Functions standard outside `S`

`IsStandardOutside F n S Φ` says two things.

1. `Φ` vanishes off `integralOutside F n S`.
2. On that set, `Φ(x)` depends only on the infinite components of the entries of `x` and
   on the local coordinates `x_v` for `v ∈ S`.

So `Φ = Φ_(S∪∞) ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)` for a function `Φ_(S∪∞)` of the coordinates at
`S` and the infinite places. This is the condition of the source objective that `Φ`
equals the characteristic function of `𝒪_v^n` at the finite places outside `S`. It is
the hypothesis on `Φ` in the unramified computation of Cogdell, Theorem 3.3, printed
p.215 (PDF p.218), where `Φ_o` is the characteristic function of `𝒪_v^n`. The definition
does not ask `Φ` to lie in `schwartzBruhat F n`; the statements that use it add this
hypothesis separately.

## The Fourier transform

`fourierTransform F n ψ Φ x` is

`Φ̂(x) = ∫_(𝔸^n) Φ(y) ψ(y ᵗx) dy`, with `y ᵗx = ∑_j y_j x_j`,

for an additive character `ψ : 𝔸 → ℂ` (a Mathlib `AddChar`). This is Cogdell's formula
on printed p.209 (PDF p.212). Cogdell writes the domain of integration as `𝔸^×`; this is
a misprint for `𝔸^n`, since `Φ` is a function on `𝔸^n`. It is also Getz–Hahn's adelic
Fourier transform (C.5), printed p.554 (PDF p.559), for `W = F^n` with the standard
pairing.

**The measure.** `dy` is `rectangleMeasure F 1 n`. This measure is published in
`Langlands.Global.RankinSelberg.WhittakerIntegrals`. It is the Library's Haar measure on
`M_(1,n)(𝔸)`, transported from the two-block unipotent subgroup of `GL_(1+n)` and
normalized so that the compact quotient `M_(1,n)(F) \ M_(1,n)(𝔸)` has volume one (under
the standing hypothesis `CompactSpace (AdeleQuotient F)`). The σ-algebra on the matrix
space is the Borel σ-algebra fixed by that module; it is part of the type of
`rectangleMeasure`, so no instance is declared here.

This is the self-dual measure for every nontrivial character `ψ` of `F \ 𝔸`. By Tate's
thesis (J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*,
1967, registered as `tate-1967-thesis`), Theorems 4.1.1 and 4.1.2, printed p.328, the
product of the local self-dual measures is self-dual on `𝔸` for Tate's standard
character. Theorem 4.1.3(2), printed pp.330–331, shows that this
measure gives `F \ 𝔸` volume one. Every other nontrivial character of `F \ 𝔸` is
`x ↦ ψ_0(αx)` for some `α ∈ F^×` (Getz–Hahn Lemma C.1.2, printed p.552), and its
self-dual measure is `|α|^(1/2)` times the old one. By the product formula
`|α| = 1`. So the self-dual measure on `𝔸` is the Haar measure of covolume one. On `𝔸^n`
with the pairing `∑_j y_j x_j`, the self-dual measure is the product measure, which
again has covolume one. Hence `rectangleMeasure F 1 n` is the self-dual measure that
Getz–Hahn use in (C.6), p.554. With this choice, Fourier inversion takes the form
`Φ̂̂(x) = Φ(-x)`, and Poisson summation holds with no constant. The Lean definition
does not depend on these facts, and the module does not prove them.

`ψ` is an arbitrary `AddChar`. The statements that use the Fourier transform add the
Library's hypotheses on `ψ` (nontrivial, unitary, trivial on `F`). Because Lean `∫` is
total, the definition asserts no integrability: `Φ̂(x)` is the Bochner integral, which is
`0` when the integrand is not integrable.

## Deviations from the sources

* The span of pure tensor functions is used instead of the abstract algebraic tensor
  product. The two have the same image in the functions on `𝔸^n`, and only that image
  is used.
* Cogdell's `𝔸^×` in the Fourier transform is read as `𝔸^n` (misprint, see above).
* No topology is put on `S(𝔸^n)`. The source uses none for these statements.
