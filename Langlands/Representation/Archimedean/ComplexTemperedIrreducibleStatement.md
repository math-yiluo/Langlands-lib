# Irreducibility of complex standard modules with exponents of equal real part

Lean module: `Langlands.Representation.Archimedean.ComplexTemperedIrreducibleStatement`.

This module was written for the proof of
`ComplexStandardLanglandsQuotientStatement` (L). It states one proposition and proves nothing.
The proposition is the input L needs at ties of the Langlands order (equal real parts of
exponents); see "Why L needs it" below.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `K = U(n)`, `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`.
`ComplexCharacterData` `d` is the character `z ↦ (z/|z|)^l |z|^(2t)` of `ℂˣ` with weight
`l = d.weight` and exponent `t = d.exponent`. `complexStandardModule n ds` is the Library's
smooth principal series `principalSeries ℂ n (complexPositionCharacter ds)`: smooth functions `f`
on `GL_n(ℂ)` with `f(diag(a) u g) = ∏ᵢ χᵢ(aᵢ) |aᵢ|_ℂ^((n-1)/2 - i) f(g)` for `u` upper unipotent,
`χᵢ` the `i`-th character of `ds` and `|z|_ℂ = |z|²` (normalized induction from the upper
triangular Borel subgroup). `complexStandardRep n ds` (right translation by `U(n)`) and
`complexStandardLie n ds` (right derivatives, extended `ℂ`-linearly to `𝔤`) act on its `U(n)`-finite
functions `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` (module
`PrincipalSeriesGKModule`). `IsIrreducibleGKModule ρ π` (module `GKModule`) says that the space
is nonzero and its only subspaces stable under all `ρ(k)` and all `π(Y)` are `0` and everything.

## The statement

`ComplexTemperedStandardIrreducibleStatement`: for every `n : ℕ` and every list `ds` of complex
characters with `ds.length = n` and `d.exponent.re = e.exponent.re` for all `d, e ∈ ds`,

`IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)`.

For `n = 0` the module is one-dimensional (functions on the trivial group) and the statement holds
trivially.

## Source

A. I. Badulescu and D. Renard, *Unitary dual of GL(n) at archimedean places and global
Jacquet–Langlands correspondence*, Compositio Math. 146 (2010) (`badulescu-renard-2010-unitary-dual`;
PDF page = printed page − 1113):

* Theorem 3.1 (printed p. 1124, PDF 11): for `d = (δ₁, …, δ_l)` with every `δᵢ` irreducible and
  square integrable modulo center (`Dᵘ`), `δ₁ × δ₂ × ⋯ × δ_l` is irreducible (and tempered). The
  authors attribute the archimedean case to the theory of R-groups (Knapp–Zuckerman 1982): for the
  groups `GL_n` the R-groups are trivial.
* §9.1 (printed p. 1132, PDF 19): for `A = ℂ`, square integrable modulo center representations
  exist only for `GL(1, ℂ)`, so `D = D₁ = Irr₁` consists of the characters
  `δ(z) = |z|^(2β) (z/|z|)^m` of `ℂˣ`; `Dᵘ` consists of the unitary ones, `Re β = 0`.

So for `GL_n(ℂ)` Theorem 3.1 says that the principal series `δ₁ × ⋯ × δ_n` of unitary characters is
irreducible. The source works with Harish-Chandra modules for `K = U(n)` (§2, printed p. 1123), as
the Library's `(𝔤, K)`-module predicates do, and `×` is normalized parabolic induction.

From the source to the statement (standard derivation, not a quotation):

* **Model.** The Library's `complexStandardModule n ds` is the smooth normalized principal series
  induced from the upper triangular Borel subgroup by the characters of `ds` in the given order,
  with `G` acting by right translation; its `U(n)`-finite part with `complexStandardRep` and
  `complexStandardLie` is its Harish-Chandra module. This is `δ₁ × ⋯ × δ_n` with `δᵢ` the `i`-th
  character of `ds` (the conventions of the Library's left-equivariant model are explained in
  `ComplexLanglandsQuotientReduction.md`).
* **Twist.** If all exponents have real part `e`, then `δᵢ = |·|^(2e) · δᵢ⁰` with `δᵢ⁰` unitary.
  Multiplication by the smooth function `g ↦ |det g|^(-2e)` (left `B`-equivariant with the
  character `∏ᵢ |aᵢ|^(-2e)`, right `U(n)`-invariant) is a linear bijection from the `U(n)`-finite
  functions of the principal series of `(δᵢ)` onto those of `(δᵢ⁰)`. It commutes with right
  translation by `U(n)`, and it intertwines the right derivatives up to adding the scalar
  `-2e Re tr(X)` to the action of `X`, which does not change the set of `(𝔤, K)`-stable subspaces.
  So irreducibility for `(δᵢ)` is irreducibility of the unitary principal series `(δᵢ⁰)`.

## Why L needs it

Let all exponents of `ds` have real part `0`. The integration pairing over `U(n)`
(`ComplexDuality.integralPairing`, published `complexStandardDuality`) between the principal series
of `ds` and of the inverse characters, composed with complex conjugation (which maps the principal
series of a unitary list to that of the inverse list), is a positive definite Hermitian form on the
`U(n)`-finite functions, invariant under `U(n)` and skew-invariant under the real Lie algebra. For a
`(𝔤, K)`-submodule `W` its orthogonal complement `W^⊥` is again a `(𝔤, K)`-submodule, and by the
finite multiplicities of `U(n)`-types the space is `W ⊕ W^⊥`. If the Langlands-ordered list `ds`
had a largest proper submodule `R` (statement L) and a proper nonzero submodule `W`, then `W ≤ R` and
`W^⊥ ≤ R`, so `R` would be everything. Hence L at such a list implies the present statement, and any
proof of L contains a proof of this one. In the Library's proof of L
(`ComplexStandardLanglandsQuotientProof`) the statement is used only at the ties of the
Langlands order: for a block parabolic subgroup whose Levi blocks collect equal real parts, the
Langlands lemma reduces L to the irreducibility of the Levi module, whose blocks are of this form.

## Provenance

Source: Badulescu–Renard 2010, Theorem 3.1 and §9.1, specialized to `GL_n(ℂ)` and to the Library's
model as explained above. The twist argument and the specialization are standard derivations, not
quotations.
