# The explicit spherical Whittaker function on `GL_(n+1)`

This module defines `sphericalWhittaker` on `GL_(n+1)(F)` with Satake parameters
`x`, using a chosen Iwasawa decomposition. The definition accepts any character
`θ`. If `IsIntegrallyTrivial v θ` holds, its value at every
`u · ϖ^λ · k`, with `u` upper unipotent and `k ∈ GL_(n+1)(O)`, is

`θ(u) · δ_B^(1/2)(ϖ^λ) · s_λ(x)` if `λ_0 ≥ λ_1 ≥ … ≥ λ_n`, and `0` otherwise,

where `s_λ` is the Schur function and `δ_B` is the modulus character of the
upper Borel subgroup. The value is the explicit formula of Shintani, in the
form given by Miyauchi (see Provenance). The module does not prove that this
function is the Whittaker function of the spherical vector of an unramified
principal series representation. That identification is a separate theorem.

The setting is the one of the published Iwasawa module
`Langlands.Representation.Whittaker.Iwasawa`. `F` is a field with a valuation
`v : Valuation F Γ₀` (Mathlib's multiplicative convention), `O = v.integer`,
and `ϖ` is a unit with `hϖ : IsUniformizingElement v ϖ`. The integral group
`GL_(n+1)(O)` is the published `integralSubgroup v.integer n`, the upper
unipotent group is `upperUnipotent (n + 1) F`, and `torus ϖ λ` is
`diag(ϖ^(λ_0), …, ϖ^(λ_n))`. A weight `λ : Fin (n + 1) → ℤ` is dominant when it
is antitone (Mathlib's `Antitone`), i.e. `λ_0 ≥ λ_1 ≥ … ≥ λ_n`. Indices start
at `0`. Characters `θ : upperUnipotent (n + 1) F →* ℂˣ` are arbitrary monoid
homomorphisms in the definition. Equivariance, right integral invariance,
normalization at `1`, and the formula for arbitrary decompositions require
`IsIntegrallyTrivial v θ`. No topology is used, except for the additive
characters in the section on standard characters.

## Functions given by their values on dominant cells

All declarations in this section are in the namespace
`Langlands.GeneralLinear.Iwasawa`.

- `unipotentPart hϖ g` is the upper unipotent factor `u` of the decomposition
  `g = u * torus ϖ λ * k` chosen by the published `exists_iwasawa`. It is the
  same choice that defines the published `exponent hϖ g`.
  `exists_eq_unipotentPart` gives an integral `k` with
  `g = unipotentPart hϖ g * torus ϖ (exponent hϖ g) * k`.
- `IsIntegrallyTrivial v θ` is the proposition that `θ u = 1` for every upper
  unipotent `u` that lies in `integralSubgroup v.integer n`, i.e. `θ` is trivial
  on the integral points of the upper unipotent group.
- `cellFunction hϖ θ c g`, for `c : (Fin (n + 1) → ℤ) → ℂ`, is
  `θ(unipotentPart hϖ g) · c(exponent hϖ g)` if `exponent hϖ g` is antitone, and
  `0` otherwise. Only the values of `c` at antitone weights matter.

The following statements assume `IsIntegrallyTrivial v θ`, except
`cellFunction_of_not_antitone`.

- `cellFunction_of_antitone`: for upper unipotent `u`, antitone `λ` and
  integral `k`,
  `cellFunction hϖ θ c (u * torus ϖ λ * k) = θ(u) · c(λ)`. So on a dominant
  cell the value does not depend on the chosen decomposition. By the
  published `exponent_eq`, the exponent of `u * torus ϖ λ * k` is `λ`. The
  published `iwasawa_unipotent_ambiguity` shows that `u` differs from the
  chosen unipotent part by an integral upper unipotent matrix, on which `θ` is
  trivial.
- `cellFunction_of_not_antitone`: if `exponent hϖ g` is not antitone, the value
  at `g` is `0`.
- `cellFunction_torus`: the value at `torus ϖ λ` is `c(λ)` if `λ` is antitone
  and `0` otherwise. `cellFunction_one`: the value at `1` is `c(0)`.
- `cellFunction_unipotent_mul`: `cellFunction hϖ θ c (u * g) = θ(u) ·
  cellFunction hϖ θ c g` for upper unipotent `u`. The exponent does not change
  (published `exponent_unipotent_mul`), and `u * g` has the decomposition with
  unipotent part `u · unipotentPart hϖ g`.
- `cellFunction_mul_integral`: `cellFunction hϖ θ c (g * k) =
  cellFunction hϖ θ c g` for integral `k`. The exponent does not change
  (published `exponent_mul_integral`).
- `cellFunction_mem`: the cell function lies in the published
  `θ`-equivariant function space
  `(equivariantFunctions (upperUnipotent (n + 1) F) θ).toSubmodule` of
  `Langlands.Representation.Whittaker.Algebraic`, whose members satisfy
  `f(u g) = θ(u) f(g)`.
- `eq_cellFunction`: let `f` be in this `θ`-equivariant space, right invariant
  under `integralSubgroup v.integer n`, and zero at `torus ϖ λ` for every
  non-antitone `λ`. Then `f` is the cell function of its torus values
  `λ ↦ f(torus ϖ λ)`. Such a function is therefore determined by its values at
  `torus ϖ λ` for antitone `λ`.

## Standard characters

Worker 31's published `standardCharacter ψ n` (module
`Langlands.Representation.Whittaker.GeneralLinear`) is
`u ↦ ψ(u_(0,1) + u_(1,2) + … + u_(n-1,n))` for a unitary additive character
`ψ : UnitaryAdditiveCharacter F`. `inverseStandardCharacter ψ n` is its
pointwise inverse. Here `F` also carries a topology, which is used only to
state `ψ`.

- `isIntegrallyTrivial_standardCharacter`: if `ψ(x) = 1` for every
  `x ∈ v.integer`, then `IsIntegrallyTrivial v (standardCharacter ψ n)`. The
  superdiagonal sum of an integral matrix is integral.
- `isIntegrallyTrivial_inverseStandardCharacter`: the same for
  `inverseStandardCharacter ψ n`.

The published `WhittakerFunctions ψ n` and `InverseWhittakerFunctions ψ n`
(module `Langlands.Representation.RankinSelberg.QuotientIntegrals`) are
abbreviations of the equivariant spaces for these two characters. When `ψ`
is trivial on `v.integer`, the preceding lemmas and `sphericalWhittaker_mem`
below give membership in those spaces. This module does not import
`QuotientIntegrals`.

## Schur functions at Satake parameters

All remaining declarations are in the namespace
`Langlands.GeneralLinear.Spherical`.

- `completeSymm σ R k` is the complete homogeneous symmetric polynomial `h_k`
  in the variables `σ`, i.e. Mathlib's `hsymm σ R k` (the sum of all monomials
  of degree `k`) for `k ≥ 0`, and `0` for `k < 0`.
- `jacobiTrudi R α`, for `α : Fin m → ℤ`, is the determinant of the `m × m`
  matrix with entries `h_(α_i - i + j)` in `m` variables.
- `satakeSchur x λ`, for `x : Fin (n + 1) → ℂˣ` and `λ : Fin (n + 1) → ℤ`, is
  `(x_0 x_1 ⋯ x_n)^(λ_n) · jacobiTrudi ℂ (λ - λ_n)` evaluated at `x`, where
  `λ - λ_n` is the weight `i ↦ λ_i - λ_n`.
- `halfModulus q λ`, for `q : ℕ`, is the complex number `(√q)^(-e)` with the
  integer exponent `e = Σ_i (n - 2i) λ_i`, i.e. `q^(-e/2)`.
- `jacobiTrudi_zero`: `jacobiTrudi R 0 = 1`. The matrix is upper triangular
  with diagonal entries `h_0 = 1`.
- `satakeSchur_zero`: `satakeSchur x 0 = 1`. `halfModulus_zero`:
  `halfModulus q 0 = 1`.

For antitone `λ`, the weight `λ - λ_n` is a partition with at most `n + 1`
parts, and `jacobiTrudi` is the right side of Macdonald's Jacobi–Trudi
identity (3.4) with `n + 1` variables. That identity makes it the Schur
polynomial `s_(λ - λ_n)(x)`, the bialternant (3.1). In (3.1), adding `c` to
every entry of a weight multiplies column `j` of the numerator
`det(x_j^(λ_i + n - i))` by `x_j^c`. So `s_λ(x) = (x_0 ⋯ x_n)^(λ_n)
s_(λ - λ_n)(x)` when `s_λ` is read as a bialternant of Laurent polynomials,
which covers weights with negative entries. Neither identity is proved here:
the definition is the determinant. It is used rather than the
bialternant because it remains valid when two parameters coincide, where the
bialternant has the form `0/0`.

For `F` with residue field of cardinality `q`, `|ϖ| = q^(-1)`, and the modulus
character `δ_B(diag(t_0, …, t_n)) = Π_(i<j) |t_i / t_j|` of the upper Borel
subgroup, one has `δ_B(ϖ^λ) = q^(-Σ_i (n - 2i) λ_i)`. So `halfModulus q λ` is
`δ_B^(1/2)(ϖ^λ)`. In Lean, `q` is an explicit natural number and is not tied to
`v` or `ϖ`.

## The spherical Whittaker function

- `sphericalWhittaker hϖ θ q x` is `cellFunction` with coefficient
  `λ ↦ halfModulus q λ · satakeSchur x λ`. For arbitrary `θ`, this specifies
  the value using `unipotentPart hϖ g` and `exponent hϖ g`, the chosen
  decomposition of `g`. If `IsIntegrallyTrivial v θ` holds, its value at every
  `u * torus ϖ λ * k` with upper unipotent `u` and integral `k` is
  `θ(u) · halfModulus q λ · satakeSchur x λ` for antitone `λ` and `0`
  otherwise. The modulus and Schur notation above applies in the source
  setting.

With `IsIntegrallyTrivial v θ`:

- `sphericalWhittaker_mem`: it lies in
  `(equivariantFunctions (upperUnipotent (n + 1) F) θ).toSubmodule`.
- `sphericalWhittaker_mul_integral`: it is right invariant under
  `integralSubgroup v.integer n`.
- `sphericalWhittaker_torus`: its value at `torus ϖ λ` is
  `halfModulus q λ * satakeSchur x λ` if `λ` is antitone, and `0` otherwise.
- `sphericalWhittaker_one`: its value at `1` is `1`.

Integral triviality is necessary for these three properties to hold together:
`θ`-equivariance, right integral invariance, and value `1` at `1`. Indeed,
for `u ∈ N ∩ GL_(n+1)(O)`, equivariance gives `W(u) = θ(u) W(1) = θ(u)`,
whereas right integral invariance gives `W(u) = W(1) = 1`. Hence `θ(u) = 1`.
This is an elementary consequence of the definitions; it is not an additional
Lean theorem in this module.

## Provenance and scope

The defining formula comes from Miyauchi:

Michitaka Miyauchi, *Whittaker functions associated to newforms for GL(n) over
p-adic fields*, J. Math. Soc. Japan 66 (2014), no. 1, 17–24,
DOI 10.2969/jmsj/06610017.

- Literature ID: `miyauchi-2014-newform-whittaker-gln`.
- SHA-256: `52d52dcca7b916e06b79a11f362a709f6e908bb25870d75bbf8083bf24c1cd68`.

Notation (Section 2, p. 18): `F` is a nonarchimedean local field of characteristic
zero, `|ϖ| = q^(-1)` with `q` the residue cardinality, `ψ` has conductor `O`
(in particular, it is trivial on `O`), `B` is the upper
Borel subgroup with unipotent radical `U`, and `ψ(u) = ψ(Σ_i u_(i,i+1))`. On
p. 19, `ϖ^f = diag(ϖ^(f_1), …, ϖ^(f_(n-1)), 1)` for `f ∈ Z^(n-1)`. Section 4,
p. 21, writes `L(s, π) = Π_i (1 - α_i q^(-s))^(-1)` and uses the Schur
polynomial `s_f` as the bialternant, citing Macdonald I.3. It also states
`δ_B(ϖ^f) = q^(-Σ_(j=1)^(n-1) (n+1-2j) f_j)`. Theorem 4.1 (p. 21) states, for
a newform `W ∈ W(π, ψ)` of an irreducible generic `π` of `GL_n(F)`, that
`W(ϖ^f) = δ_B^(1/2)(ϖ^f) s_f(α) W(1)` if `f_1 ≥ … ≥ f_(n-1) ≥ 0`, and `0`
otherwise. Its proof says that for conductor `c(π) = 0` (`π` unramified, `W`
spherical) the theorem follows from Shintani 1976. Remark 4.3 (p. 22) extends
the formula to `U Z D_1 K_(c(π))` by the central character.

The relation of `sphericalWhittaker` to this theorem is derived, as follows.

- The Lean rank is `n + 1`. Shifting Miyauchi's `1`-based index `j` to the
  `0`-based `i = j - 1` turns `n + 1 - 2j` in rank `n` into `n - 2i` in rank
  `n + 1`.
- Only the unramified case is formalized. The Satake parameters are
  `x : Fin (n + 1) → ℂˣ`, all nonzero, as are the `α_i` when `L(s, π)` has full
  degree. `ϖ^λ` ranges over all of `Z^(n+1)`, not only over weights with last
  entry `0`. The extension to all of `Z^(n+1)` uses the central character, as
  in Remark 4.3: adding `c` to every entry of `λ` multiplies the value by
  `(x_0 ⋯ x_n)^c`. This is the value at `ϖ` of the central character of the
  unramified principal series with Satake parameters `x`, a standard fact that
  is not formalized and not stated in the sources cited here. It does not change
  `δ_B^(1/2)`, because `Σ_i (n - 2i) = 0`. Under this extension, the formula
  in `sphericalWhittaker_torus` for weights with `λ_n = 0` is Miyauchi's
  formula with `c(π) = 0` and `W(1) = 1`.
- The general character `θ` and the general valued field are derived
  generalizations. The source case is `θ = standardCharacter ψ n` with `ψ` of
  conductor `O`, `v` the valuation of a nonarchimedean local field of
  characteristic zero, and `q` its residue cardinality. For other `θ`, `v`
  or `q`, with the stated uniformizing-element hypothesis, the choice-defined
  function still exists. Under `IsIntegrallyTrivial v θ`, it is
  `θ`-equivariant, right `GL_(n+1)(O)`-invariant and has value `1` at `1`;
  the arbitrary-decomposition and torus formulas also retain this hypothesis.
  These conclusions are not asserted for arbitrary `θ`. No further
  representation-theoretic identification is claimed for the generalization.
- The vanishing off antitone weights is built into `cellFunction`. In the
  source it is a theorem about Whittaker functions. Here it is part of the
  definition.
- Formalizing the theorem that `sphericalWhittaker` is the Whittaker function
  of the normalized spherical vector is left open. This is Shintani's
  characterization through the Hecke eigen-equations, and the function
  `W(g; x; ψ)` of Jacquet (2012), p. 516, with `x_i = q^(-t_i)`.

Schur functions follow Macdonald:

I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd edition,
Oxford Mathematical Monographs, Oxford University Press, 1995.

- Literature ID: `macdonald-1995-symmetric-functions`.
- SHA-256: `64e242b84d1f3b7864ed28f89a9b331269a28c1ce2a32ce03b4ee692f5974ea7`.

Chapter I, Section 2, p. 21 defines `h_r` as the sum of all monomials of
degree `r`, with `h_0 = 1` and `h_r = 0` for `r < 0`. Section 3, p. 40, (3.1)
defines `s_λ = a_(λ+δ) / a_δ` in `n` variables for a partition `λ` of length at
most `n`. On p. 41, (3.4) is the Jacobi–Trudi identity
`s_λ = det(h_(λ_i - i + j))_(1 ≤ i, j ≤ n)` for `n ≥ l(λ)`. `completeSymm` is
this `h_r`, and `jacobiTrudi` is the right side of (3.4) with `0`-based
indices; shifting `i` and `j` by the same amount does not change
`λ_i - i + j`.

The cell-function construction and its lemmas, the integral-triviality
predicate and the standard-character lemmas are internal. They implement
Shintani's remark (1976, p. 180, literature ID
`shintani-1976-class-one-whittaker`) that a function of this kind is
determined by its values `w(f) = W(π^f)`.

## Dependencies

Imports are the modules published in Library commit
`f5f825f762f6e1cbbb8ec9161e74894398fdbd14`:
`Langlands.Representation.Whittaker.Iwasawa` (`exists_iwasawa`, `exponent`,
`exponent_eq`, `exponent_torus`, `exponent_mul_integral`,
`exponent_unipotent_mul`, `iwasawa_unipotent_ambiguity`, `torus`,
`diagonalUnits`, `IsUniformizingElement`) and
`Langlands.Representation.Whittaker.GeneralLinear` (`standardCharacter`,
`inverseStandardCharacter`, and through its imports `equivariantFunctions`
and `UnitaryAdditiveCharacter`), together with
`Mathlib.RingTheory.MvPolynomial.Symmetric.Defs` (`hsymm`). Environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Worker 43 authored this module.
