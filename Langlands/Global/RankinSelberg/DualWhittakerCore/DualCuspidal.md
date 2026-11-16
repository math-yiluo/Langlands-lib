# Cuspidality of the transpose-inverse dual

Module `Langlands.Global.RankinSelberg.DualWhittakerCore.DualCuspidal`, namespace
`Langlands.Automorphic`. This helper module is internal to the proof of
`DualCuspidalWhittakerExpansionStatement` (module `DualWhittakerExpansionProof`). Provenance:
internal. It proves the standard fact that `g ↦ f(ᵗg⁻¹)` is cuspidal when `f` is cuspidal. For
cusp forms this is part of the statement that `φ̃(g) = φ(w_n ᵗg⁻¹)` is a cusp form in the
contragredient (Cogdell 2004, printed p.206, source `cogdell-2004-analytic-theory-gln`); the
proof here is a direct computation of constant terms.

Notation. `K` is a number field with `𝔸_K/K` compact, `AdelicGL K n = GL_n(𝔸_K)`,
`ContinuousRationalFunctions K n` are the continuous functions on `GL_n(𝔸_K)` that are left
invariant under `GL_n(K)`, `inverseTranspose n R g = ᵗg⁻¹`, `permutation n R σ` is the
permutation matrix of `σ`, and `blockUnipotent h X` (for `h : a + b = n` and an `a × b`
matrix `X`) is the block unipotent `[[1, X], [0, 1]]`. `constantTerm K n h f g` is the Library
constant term of `f` along the `(a, b)` block parabolic: the integral of `f(u(X) g)` over
`X ∈ M_(a×b)(𝔸_K/K)` against the normalized Haar measure `matrixQuotientHaar K a b`, and
`IsCuspidal K n f` says that all constant terms with `0 < a`, `0 < b` vanish.

## Matrices (section `Matrices`, any commutative ring `R`)

* `blockEquiv h : Fin a ⊕ Fin b ≃ Fin n` is the consecutive block numbering used by
  `blockUnipotent`.
* `blockSwap h : Equiv.Perm (Fin n)` exchanges the blocks: it sends the `(b, a)` index of `p` to
  the `(a, b)` index of `p.swap`. `blockSwap_inv_apply` computes its inverse on `(a, b)` indices.
* `blockUnipotent_apply_blockEquiv`: the entries of `blockUnipotent h X` in block indices are
  those of `Matrix.fromBlocks 1 X 0 1`.
* `blockUnipotent_inv`: `u(X)⁻¹ = u(-X)`.
* `inverseTranspose_blockUnipotent`: `ᵗu(Y)⁻¹ = P u'(-ᵗY) P⁻¹`, where `u'` is the `(b, a)` block
  unipotent and `P = permutation n R (blockSwap h)`. The proof compares entries in block indices,
  in the four block cases.
* `map_permutation`: permutation matrices are compatible with ring homomorphisms.

## Rational matrices

* `inverseTranspose_rational`: transpose inverse commutes with the embedding
  `AdelicGL.rational` of `GL_n(K)` into `GL_n(𝔸_K)` (the Library
  `UnequalAnalytic.inverseTranspose_map`).
* `permutation_eq_rational`: an adelic permutation matrix is the image of the rational one.

## The dual function

* `ContinuousRationalFunctions.transposeDual f` is the function `x ↦ f(ᵗx⁻¹)`, as an element of
  `ContinuousRationalFunctions K n`: it is left invariant under `GL_n(K)` because
  `ᵗ(γ x)⁻¹ = ᵗγ⁻¹ ᵗx⁻¹` with `ᵗγ⁻¹` rational, and continuous because transpose inverse is.
* `evaluate_transposeDual` (simp, `rfl`): its value at `x` is `f(ᵗx⁻¹)`.

## Measures (section `Measure`)

* `transposeNegEquiv K a b` is the continuous additive equivalence `X ↦ -ᵗX` from
  `M_(a×b)(𝔸_K/K)` to `M_(b×a)(𝔸_K/K)`, with `transposeNegEquiv_apply`.
* `map_transposeNegEquiv_matrixQuotientHaar`: it carries `matrixQuotientHaar K a b` to
  `matrixQuotientHaar K b a` (both spaces with their Borel σ-algebras). The image of an additive
  Haar measure under a continuous additive equivalence is an additive Haar measure, and both
  measures are probability measures, so Mathlib's
  `Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure` identifies them.
* `integral_transposeNegEquiv`: the corresponding change of variables in integrals.

## Constant terms

* `matrixQuotientMap_neg_transpose`: reduction modulo `K` commutes with `Y ↦ -ᵗY`.
* `constantTerm_transposeDual`: the `(a, b)` constant term of `transposeDual f` at `g` is the
  `(b, a)` constant term of `f` at `P⁻¹ ᵗg⁻¹`, with `P` the rational permutation matrix of
  `blockSwap h`:
  `f(ᵗ(u(X) g)⁻¹) = f(P u'(-ᵗX) P⁻¹ ᵗg⁻¹) = f(u'(-ᵗX) P⁻¹ ᵗg⁻¹)` by left invariance under the
  rational `P`, and the change of variables `X ↦ -ᵗX` turns the integral over `X` into the
  `(b, a)` constant term.
* `isCuspidal_transposeDual`: if `f` is cuspidal, then `transposeDual f` is cuspidal. The `(a, b)`
  constant term of the dual is a `(b, a)` constant term of `f`, and `0 < b`, `0 < a`.
