# Intertwiners to the reversed standard module: the strictly ordered case

Lean module: `Langlands.Representation.Archimedean.ComplexReverseIntertwinerStrict`.

Notation. `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` with Haar
probability measure `ComplexDuality.unitaryHaar n`. For a list `ds` of `ComplexCharacterData`,
`I(ds)` is the `(𝔤𝔩_n(ℂ), U(n))`-module `(complexStandardRep n ds, complexStandardLie n ds)` on
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`: the `U(n)`-finite functions
of the smooth principal series of the characters `χ_j = complexPositionCharacter ds j` (the
character of the `j`-th entry of `ds`). An intertwiner `T : I(ds) → I(es)` is a `ℂ`-linear map
with `IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds T`.
`ComplexStrictLanglandsQuotient.IsStrictlyOrdered ds` (Library) says that the real parts of the
exponents of `ds` strictly decrease along the list.

## The statement

`Langlands.Archimedean.ComplexStrictReverseIntertwinerKernelStatement`. For every `n`, every list
`ds` of `n` complex characters with `IsStrictlyOrdered ds`, every intertwiner
`T : I(ds) → I(ds.reverse)` and every `(𝔤, K)`-submodule `W` of `I(ds)` (`IsGKSubmodule`) with
`W ≠ ⊤`, we have `W ≤ ker T`.

It is proved by `Langlands.Archimedean.complexStrictReverseIntertwinerKernel`, which applies
`ComplexReverseIntertwinerStrict.le_ker_of_isStrictlyOrdered`.

### Provenance

Derived (internal). This is the special case, for strictly decreasing real parts of the exponents,
of `ComplexReverseIntertwinerKernelStatement` (Rev_C), stated in the module
`ComplexStandardIrreducibleCriterionReduction`; the hypothesis `IsStrictlyOrdered ds` replaces `IsComplexLanglandsOrdered ds`
(non-increasing real parts), and everything else is identical. The Markdown of that module
explains the background in Langlands' classification: the image of a nonzero intertwiner
`I(ds) → I(ds.reverse)` is the Langlands quotient, so its kernel is the largest proper submodule.
The formal proof below does not follow that route; it uses the Jacquet integral of the published
modules `ComplexJacquetDual`, `ComplexJacquetKernel` and `ComplexJacquetNonvanishing`.

## Supporting modules

- `ComplexReverseTwist`: the twist `twist g = w₀ (gᵀ)⁻¹`, invariance of the Haar
  measure of `U(n)` under it, and pullback of principal series along it.
- `ComplexJacquetLimitSum`: the limit argument of `ComplexJacquetLimit` for two pairs
  of functions, with the hypothesis only on the ray `d(s) = diag(1, …, 1, s)`.
- `ComplexReverseRecursion`: `integral_mul_swap` and the recursion
  `mul_jacquet_eq_of_transpose`: if `∫ x₁(κ g) y₁(κ) dκ = ∫ x₂(κ gᵀ) y₂(κ) dκ` for all `g`, then
  `x₁(1) Λ_n(y₁) = x₂(1) Λ_n(y₂)` (`Λ_n` the Jacquet integral in stages, strictly dominant
  exponents).
- `ComplexReverseTransfer`: the pairing transpose `exists_pairing_transpose` and the
  transfer identity `integral_mul_transfer`.

## Results of this module

- `complexPositionCharacter_inv`: `complexPositionCharacter ds i z⁻¹ = (complexPositionCharacter ds i z)⁻¹`.
- `complexPositionCharacter_reverse`: if `ds.length = n`, the position character of `ds.reverse`
  at `n - 1 - j` is that of `ds` at `j`.
- `le_ker_of_isStrictlyOrdered n ds T W hn hord hT hW hW' : W ≤ LinearMap.ker T`, with the
  hypotheses of the statement.

## Proof of `le_ker_of_isStrictlyOrdered`

Let `χ`, `ψ` be the position characters of `ds` and `ds.reverse`. Both are phase-power
characters (`isPhasePower`), and the exponents of `χ` are strictly dominant
(`ComplexStrictLanglandsQuotient.isStrictlyDominant`). Write `χ⁻¹ = dualChar χ`. The two
reindexing identities `ψ⁻¹_j(z) = χ_{n-1-j}(z⁻¹)` and `χ⁻¹_j(z) = ψ_{n-1-j}(z⁻¹)` follow from the
two lemmas above.

1. The Jacquet integral vanishes on `W`. View `W` as a space of functions on `GL_n(ℂ)`. It is
   stable under right translation by `U(n)` and under right derivatives (the `(𝔤, K)`-stability
   of `W`), and some `U(n)`-finite principal series vector is not in `W` since `W ≠ ⊤`. So
   `ComplexJacquetKernel.jacquet_eq_zero_of_proper` gives `Λ_n(w) = 0` for `w ∈ W`.
2. A test vector. `ComplexJacquetNonvanishing.exists_jacquet_ne_zero` gives a `U(n)`-finite `f`
   in the principal series of `χ` with `Λ_n(f) ≠ 0`. Put `v = f ∘ twist`; by
   `twistLin_mem_kFiniteFunctions` and the first reindexing identity, `v` lies in the
   `U(n)`-finite principal series of `ψ⁻¹`.
   `exists_pairing_transpose` gives `u` in the `U(n)`-finite principal series of `χ⁻¹` with
   `⟨u, h⟩ = ⟨v, T h⟩` for all `h ∈ I(ds)`.
3. A transposed identity. For `w ∈ W` and `g ∈ GL_n(ℂ)`,
   `∫ u(κ g) w(κ) dκ = ∫ w(κ g⁻¹) u(κ) dκ` (`integral_mul_swap` at `g⁻¹`)
   `= ∫ (T w)(κ g⁻¹) v(κ) dκ` (`integral_mul_transfer` at `g⁻¹`)
   `= ∫ (T w)(twist(κ gᵀ)) f(κ) dκ` (`integral_mul_inv_eq_twist` and `twist_twist`).
   The function `(T w) ∘ twist` lies in the `U(n)`-finite principal series of `χ⁻¹` (second
   reindexing identity).
4. The recursion `mul_jacquet_eq_of_transpose` with `x₁ = u`, `y₁ = w`, `x₂ = (T w) ∘ twist`,
   `y₂ = f` gives `u(1) Λ_n(w) = (T w)(twist 1) Λ_n(f) = (T w)(w₀) Λ_n(f)`. By step 1 the left
   side is `0`, and `Λ_n(f) ≠ 0`, so `(T w)(w₀) = 0` for every `w ∈ W`.
5. Let `w ∈ W` and `k ∈ U(n)`. Then `R(w₀ k) w ∈ W`, and `T` commutes with `R(w₀ k)`, so
   `0 = (T R(w₀ k) w)(w₀) = (T w)(w₀ w₀ k) = (T w)(k)`. Thus `T w` vanishes on `U(n)`, hence
   everywhere (`ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`, Iwasawa decomposition).
   So `W ≤ ker T`.
