# Transposition of intertwinings between complex principal series

This module was written for the proof of the Library's
`Langlands.Archimedean.ComplexLanglandsQuotientUniqueStatement`. The
module states one statement (TP). It proves nothing. The declaration is in the namespace
`Langlands.Archimedean`. It imports `Langlands.Representation.Archimedean.PrincipalSeriesGKModule`
and `Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction`; the latter gives
`complexCharacterDataInv`.

The Library names are as in `ComplexStandardHomExponent.md`. In particular, for a list `ds` of
`n` complex characters, `X(ds)` is
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`, the `U(n)`-finite
functions of the principal series of `ds`. The predicate
`IsComplexStandardIntertwining n (complexStandardRep n cs) (complexStandardLie n cs) ds T`
says that `T : X(ds) → X(cs)` commutes with right translation by `U(n)` and with right
derivatives along real directions of `𝔤𝔩_n(ℂ)`. `complexCharacterDataInv d` is the inverse
character `z ↦ (z/‖z‖)^{-l} ‖z‖^{-2t}` (character `d.character⁻¹`, weight `-d.weight`,
exponent `-d.exponent`; see `ComplexLanglandsQuotientReduction.md`).

## Statement TP: `ComplexStandardHomTransposeStatement`

For every `n : ℕ`, all `d c : Fin n → ComplexCharacterData` and every `ℂ`-linear map
`T : X(List.ofFn d) → X(List.ofFn c)` such that `T ≠ 0` and
`IsComplexStandardIntertwining n (complexStandardRep n (List.ofFn c))
(complexStandardLie n (List.ofFn c)) (List.ofFn d) T`, there is a `ℂ`-linear map
`T' : X(List.ofFn (c⁻¹)) → X(List.ofFn (d⁻¹))`, where `c⁻¹ = fun j => complexCharacterDataInv (c j)`
and `d⁻¹` likewise, such that `T' ≠ 0` and
`IsComplexStandardIntertwining n (complexStandardRep n (List.ofFn d⁻¹))
(complexStandardLie n (List.ofFn d⁻¹)) (List.ofFn c⁻¹) T'`.

**Meaning.** A nonzero `(𝔤, K)`-map `X(d) → X(c)` gives a nonzero `(𝔤, K)`-map
`X(c⁻¹) → X(d⁻¹)` in the opposite direction, between the principal series of the pointwise
inverse characters. The intended `T'` is the transpose of `T` under the contragredient
dualities `X(c)^∨ ≅ X(c⁻¹)` and `X(d)^∨ ≅ X(d⁻¹)`. The statement only asserts that some
nonzero map exists.

**Provenance.** Derived. TP is an intermediate statement of the uniqueness proof for
`ComplexLanglandsQuotientUniqueStatement` and no cited source states it in this form. It is the standard fact that the `U(n)`-finite
dual of a principal series is the principal series of the inverse character. The expected
proof runs as follows.

1. The standard pairing `⟨f, h⟩ = ∫_{U(n)} f(k) h(k) dk` of `X(ds)` with `X(ds⁻¹)` is invariant
   under right translation by `U(n)` and under right derivatives. It is nondegenerate in the
   second argument. This much is the Library's `ComplexStandardDualityStatement` (module
   `ComplexLanglandsQuotientReduction`). The same argument gives nondegeneracy in the first
   argument.
2. Each `U(n)`-isotypic component of `X(ds)` is finite-dimensional (the restriction of a
   principal series to `U(n)` is induced from the diagonal torus of `U(n)`, so by Frobenius
   reciprocity each `U(n)`-type occurs with finite multiplicity). The pairing makes the
   `τ`-isotypic component of `X(ds⁻¹)` the dual of the `τ^∨`-isotypic component of `X(ds)`.
   So every `U(n)`-finite linear functional on `X(ds)` is `⟨·, h⟩` for a unique
   `h ∈ X(ds⁻¹)`.
3. For `f ∈ X(c⁻¹)`, the functional `h ↦ ⟨f, T h⟩` on `X(d)` is `U(n)`-finite, because `T`
   commutes with `U(n)`. By step 2 it is `⟨T' f, ·⟩` for a unique `T' f ∈ X(d⁻¹)`. The map `T'`
   is linear and intertwines, because the pairings are invariant and `T` intertwines.
4. `T' ≠ 0`: pick `h` with `T h ≠ 0`, then `f` with `⟨f, T h⟩ ≠ 0` (nondegeneracy in the second
   argument). Then `⟨T' f, h⟩ ≠ 0`.

For irreducible admissible modules the Library's `ComplexContragredientStatement` (module
`ComplexLanglandsQuotientReduction`) asserts the analogous duality. There the representability
of `U(n)`-finite functionals is one of the clauses the statement asserts; for principal series
it comes from step 2.

## Use

The follow-up module `ComplexStandardOppositeOrderHomReduction` applies TP to a
nonzero map `T : X(d) → X(c)` and then applies `ComplexStandardHomExponentStatement` (module
`ComplexStandardHomExponent`) to both `T` and `T'`. Since the exponents of `c⁻¹` and `d⁻¹`
are the negatives of those of `c` and `d`, this bounds the real parts of the exponents of `d`
by those of `c` in the opposite dominance order. Together with E this proves
`ComplexStandardOppositeOrderHomStatement`, the statement from the module
`ComplexLanglandsQuotientUniqueReduction`.
