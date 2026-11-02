# Subfields of Galois CM fields containing an imaginary square root

Module `Langlands.Global.Arithmetic.CMSubfield`, namespace
`Langlands.Global.CMRealization`. These are supporting lemmas for the proof of
`Langlands.Global.HarrisPairedPlaceRealizationStatement`. The only definition is the
automorphism `conjQ`; everything else is a theorem. The module adds no assumptions.

## Provenance

The facts are standard CM-field arguments. Henniart (2000), Section 3.3, printed page 449
(registered source `henniart-2000-simple-proof`), and Harris (1998), Section 4, printed pages
200–201 (registered source `harris-1998-local-langlands`), use them without proof when they take
composita of a totally real field with an imaginary quadratic field. The proofs below use Mathlib's
`NumberField.IsCMField`, `maximalRealSubfield` and `IsCMField.complexConj`, and the published
Library module `QuadraticRootSupport` (`squareRoot_finrank`).

## Central automorphisms

`mem_of_central`: let `M` be a Galois number field and `u` an automorphism of `M` over `ℚ` that
commutes with every automorphism of `M`. Then `u` maps every intermediate field `S` of `M / ℚ`
into itself. The proof writes `S` as the fixed field of its fixing subgroup (Galois
correspondence) and checks that `u x` is fixed by each `σ` fixing `S`, because `σ (u x) =
u (σ x) = u x`.

## Square roots of negative rationals

Fix a rational `a < 0` and an element `x` of a characteristic-zero field `K` with `x² = a`.

- `complex_sq_ne_of_isReal`: a complex number fixed by complex conjugation is real, so its square
  is not `a`.
- `isTotallyComplex_of_sq_neg`: every infinite place of a number field `K` containing `x` is
  complex, since a real embedding would send `x` to a real square root of `a`.
- `not_mem_maximalRealSubfield_of_sq_neg`: if `K` has a complex embedding, then `x` is not totally
  real, for the same reason.
- `isCMField_of_adjoin_eq_top`: if `K` has a complex embedding and `K = K⁺(x)`, where `K⁺` is the
  maximal real subfield, then `K` is a CM field. The field `K` is totally complex by the second
  point. The image of `a` in `K⁺` is not a square: a square root `b ∈ K⁺` of it would satisfy
  `b = ±x`, putting `x` in `K⁺`. So `[K : K⁺] = 2` by `squareRoot_finrank`, which is Mathlib's
  quadratic condition in `IsCMField`.

## Complex conjugation as a rational automorphism

For a CM field `M`, `conjQ M` is `IsCMField.complexConj M` viewed as an automorphism of `M` over
`ℚ`. The lemmas record that it is an involution (`conjQ_conjQ`), that every complex embedding
`φ` satisfies `φ (conjQ M x) = conj (φ x)` (`embedding_conjQ`), and that its fixed elements are the
totally real ones (`conjQ_eq_self_iff`). `conjQ_central`: it commutes with every automorphism
`σ` of `M`. Both sides have the same image under a complex embedding `φ`, namely the complex
conjugate of `φ (σ x)`, because `φ ∘ σ` is again a complex embedding. `conjQ_of_sq_neg`: it
sends a square root `x` of `a < 0` to `-x`. Its image is a square root of `a`, hence `±x`, and
`x` itself is not fixed because it is not totally real.

## Fields mapping into a CM field

Let `M` be a CM number field and `S` a characteristic-zero field with an algebra map `S → M`.
Assume that the image of `S` is stable under `conjQ M` (hypothesis `hS`). Assume also that `S`
contains a square root `x` of a rational `a < 0`.

- `mem_maximalRealSubfield_of_conjQ`: if the image of `y ∈ S` is fixed by `conjQ M`, then `y` is
  totally real. Every complex embedding `ψ` of `S` extends to `M`
  (`ComplexEmbedding.lift`), and `embedding_conjQ` applied to the extension shows that `ψ y` is
  real.
- `exists_real_decomposition`: every `y ∈ S` is `y₁ + y₂ x` with `y₁, y₂` totally real. Let `z`
  be the element of `S` whose image is `conjQ M` of the image of `y`. Take `y₁ = (y + z) / 2` and
  `y₂ = (y - z) / (2x)`. Both are fixed by conjugation in `M`, using `conjQ M x = -x`. So both are
  totally real by the previous point.
- `isCMField_of_sq_neg`: `S` is a CM field. By the decomposition, `S = S⁺(x)`. Then
  `isCMField_of_adjoin_eq_top` applies, since `S` has the complex embedding obtained from `M`.
- `maximalRealSubfield_sup_eq_top`: for every subfield `T` of `S` containing `x`, the join of
  `T` with the maximal real subfield of `S` is all of `S`. This is again the decomposition.
- `algebraMap_complexConj`: when `S` is a CM number field, its complex conjugation is the
  restriction of `conjQ M`. The two sides agree after composing with any complex embedding of
  `M`, by the defining property of complex conjugation on `S` and on `M`.
