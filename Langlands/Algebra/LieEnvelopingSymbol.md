# Symbols of enveloping elements through ordered PBW coordinates

Module `Langlands.Algebra.LieEnvelopingSymbol`, namespace `Langlands.Algebra.LieEnvelopingSymbol`.

Let `k` be a field, `L` a `k`-Lie algebra with a finite basis `b : Basis I k L`, and `bs` a
duplicate-free list containing every index. The ordered monomials along `bs` form the basis
`orderedMonomialBasis b hbs hall` of the universal enveloping algebra `U = U(L)` (module
`Langlands.Algebra.OrderedMonomialBasis`). This module defines symbols of elements of `U` from
their coordinates in that basis, for an arbitrary Lie algebra; the Library's
`Langlands.Archimedean.Kostant.SymbolData` provides symbols only through a representation by
derivations, as for associative algebras.

## Definitions

- `pbwPoly b hbs hall : U →ₗ[k] MvPolynomial I k` sends the ordered monomial with exponent `α`
  to the monomial `X^α` (`pbwPoly_orderedMonomial`). Its coefficients are the PBW coordinates
  (`coeff_pbwPoly`).
- `symbol b hbs hall N` is the homogeneous component of degree `N` of `pbwPoly`
  (`coeff_symbol`, `symbol_orderedMonomial`).
- `ξ b : L →ₗ[k] MvPolynomial I k` sends `x` to the linear form `∑ c, b.repr x c • X c`
  (`ξ_basis`, `ξ_apply`).
- `adDer b y` is the derivation of `MvPolynomial I k` with `X c ↦ ξ ⁅y, b c⁆`; it satisfies
  `adDer b y (ξ z) = ξ ⁅y, z⁆` (`adDer_ξ`).

## Results

Write `U_N` for the Library's `degreeFiltration k L N` (spanned by products of at most `N`
generators).

- `coeff_pbwPoly_eq_zero_of_mem`: an element of `U_N` has no PBW coordinate of degree above
  `N`. The Library's `degreeFiltration_le_orderedSpan` puts `U_N` in the span of the ordered
  monomials of degree at most `N`.
- `symbol_eq_zero_of_mem`: `symbol N` vanishes on `U_M` for `M < N`.
- `symbol_generator_mul`: for `P ∈ U_M`, `symbol (M+1) (ι (b c) * P) = X c * symbol M P`. It
  suffices to take `P` an ordered monomial of degree at most `M`. If the degree is smaller, both
  sides vanish. Otherwise `ι (b c)` times the monomial is a word that is a permutation of the
  ordered monomial with exponent `α + single c 1`; the Library's `word_sub_word_mem_of_perm`
  puts the difference in `U_M`, and `perm_expand` identifies the permuted word.
- `symbol_ι_mul`: the same with `ξ x` for any `x ∈ L`, by linearity in `x`.
- `symbol_word_of_length_eq`, `symbol_word_of_length_lt`, `symbol_one`: a word of length `N`
  has symbol the product of the `ξ` of its letters; shorter words have symbol `0`.
- `symbol_mul`: `symbol (a+c) (P * Q) = symbol a P * symbol c Q` for `P ∈ U_a`, `Q ∈ U_c`.
- `symbol_commutator`: for `P ∈ U_N` and a derivation `δ` with `δ (ξ y) = ξ ⁅x, y⁆`,
  `symbol N (ι x * P - P * ι x) = δ (symbol N P)`, by induction on words. The special case
  `δ = adDer b x` is `symbol_commutator_adDer`.
- `mem_degreeFiltration_of_symbol_eq_zero`: an element of `U_{N+1}` with vanishing symbol of
  degree `N + 1` lies in `U_N`; `eq_zero_of_mem_zero_of_symbol_eq_zero` is the case `N = 0`.

The proofs of `symbol_mul` and `symbol_commutator` follow those of the corresponding statements
for `SymbolData` in `Langlands.Archimedean.Kostant.Symbol`; only the base facts about words are
proved differently, from the ordered PBW basis.

## Provenance

Internal construction. Symbols with respect to the degree filtration are the classical
identification of the associated graded algebra of `U(L)` with the symmetric algebra (the
Poincaré–Birkhoff–Witt theorem); here they are realized concretely by PBW coordinates.
