# Tempered blocks with real exponents over a nonarchimedean local field

Module `Langlands.AllField.Representation.RankinSelberg.TemperedTypeDatum`, namespace
`Langlands.AllField.RankinSelberg`.

The field `F` is any field with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`, of any characteristic. The module defines the data of
JPSS 1983, Proposition (9.4) (printed page 458), with the order of the exponents relaxed
to a non-strict one, and the two operations on them used in the proof of (9.4): deleting
the first block, and reversing the blocks after pulling them back by inverse transpose.

## Predicates and characters

- `IsTemperedRepresentation ρ` for a representation `ρ` of `GL_n(F)`: for every Haar
  measure `μ` on the Borel structure of `GL_n(F) / Z`, `IsTemperedModCenter ρ μ`
  (admissible, a unitary central character, and matrix coefficients in `L^(2+ε)` modulo
  the center for every `ε > 0`). This is the formula of the Library's p-adic
  `PadicField.TopologicalData.IsTempered`, with the ambient topology of `F`.
  `IsTemperedRepresentation.comp_continuousMulEquiv`: it is preserved by pullback along a
  continuous automorphism (published generic `isTemperedModCenter_comp_continuousMulEquiv`).
- `IsOfRankWhittakerType ψ π`: Whittaker type for the standard character at an arbitrary
  rank (false at rank zero); `isOfRankWhittakerType_succ` unfolds it at rank `r + 1`, and
  `IsOfRankWhittakerType.of_equiv` transports it along equivalences.
- `determinantPowerCharacter n s`: `g ↦ |det g|^s`, the published `realPowerCharacter` of
  the determinant norm of `(⟨⟩ : LocalFieldData F)`. Its kernel is open, it is trivial on
  the upper unipotent subgroup, and inverse transpose negates `s`
  (`determinantPowerCharacter_inverseTranspose`).
- `isOfRankWhittakerType_twist_iff`: twisting by a determinant power preserves Whittaker
  type (published `isOfWhittakerType_twist_iff`).
- `isOfRankWhittakerType_inverseTranspose`: inverse transpose turns Whittaker type for
  `ψ⁻¹` into Whittaker type for `ψ` (published `isOfWhittakerType_inverseTransposePullback`
  and `inverseStandardCharacter_scale_neg_one`).

## The datum

`TemperedTypeDatum n` consists of an ordered block shape `(n_1, …, n_r)` of `n`, smooth
representations `τ_i` of `GL_(n_i)(F)` that are irreducible, tempered and of Whittaker
type for every nontrivial additive character `ψ`, and real exponents with
`u_1 ≥ ⋯ ≥ u_r` (`Antitone`).

- `twistedBlock i`: `τ_i ν^(u_i)`, the twist by `determinantPowerCharacter n_i u_i`;
  `twistedBlock_whittaker` gives its Whittaker type.
- `standardModule`: `Ind(τ_1 ν^(u_1), …, τ_r ν^(u_r))`, the normalized induction
  `(⟨⟩ : LocalFieldData F).normalizedProductInduced` from the standard upper block
  parabolic.
- `tail h`, for `h : shape.length = k + 2`: the datum without the first block;
  `tail_length_lt`. `headTailStandardModuleEquiv h`: the standard module is the
  normalized two-block induction of the first twisted block (lifted to the carrier
  universe) and the standard module of the tail (published all-field
  `headTailProductInductionEquiv`); `headTailStandardFactors_one` identifies the second
  factor.
- `inverseTranspose`: blocks `τ_(r+1-i)` pulled back by inverse transpose, exponents
  `-u_(r+1-i)`. Irreducibility, temperedness and antitonicity are preserved; Whittaker
  type for `ψ` comes from Whittaker type of `τ` for `ψ⁻¹`.
- `normalizedProductInverseTranspose`: for any family of smooth blocks, the pullback of
  their normalized product by inverse transpose is the normalized product of the reversed
  family of pulled-back blocks. It composes the published all-field
  `inverseTransposeProductToOppositeEquiv` and `glOppositeProductReversal`, as the
  Library's p-adic `Parabolic.normalizedProductInverseTranspose` does.
- `inverseTransposeTwistedBlockEquiv`, `inverseTransposeStandardModuleEquiv`: the pullback
  of the standard module by inverse transpose is the standard module of `inverseTranspose`.

Source: JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), Proposition (9.4), printed
pages 458–462. JPSS state (9.4) for `u_1 > ⋯ > u_r`. The proof of (9.4) in
`temperedTypeLPolynomial_product`, like the Library's p-adic proof `langlandsTypeLFactor`,
uses the exponents only through `u_i ≥ u_j` for `i ≤ j`, so the non-strict order is
allowed; it admits, for instance, unramified characters with equal absolute values. The construction follows the
Library's p-adic `PadicField.TopologicalData.TemperedLanglandsDatum` and its modules
`LanglandsTailDatum`, `LanglandsHeadTailStandardModule` and
`LanglandsInverseTransposeDatum`.
