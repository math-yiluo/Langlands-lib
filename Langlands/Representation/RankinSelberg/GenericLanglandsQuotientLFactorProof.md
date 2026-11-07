# Generic Langlands quotients have the L-factor of their standard modules

Author: Worker 1789.

This module proves `GenericLanglandsQuotientLFactorStatement` (JPSS 1983,
(9.4), display (4), printed page 458), stated in
`LanglandsQuotientLFactorStatement`. The theorem is
`Langlands.RankinSelberg.genericLanglandsQuotientLFactor`, with universe
parameters `uF`, `uV`, `uW`.

Take tempered Langlands data `d`, `e`, irreducible quotients `π` of
`d.standardModule` and `σ` of `e.standardModule`, and assume `π` and `σ`
generic. The theorem gives one polynomial `P` that is the symmetric
L-polynomial of the two standard modules and also of `(π, σ)`.

## Route

JPSS argue that `π` and its standard module `ξ` "have the same Whittaker
model". They use the fact that tempered representations are generic, together
with (2.3), to see that `ξ` is of Whittaker type. Neither fact is in the
Library. The Lean proof avoids both. It shows that `ξ` is of Whittaker type
because it has a generic quotient, using the published finite-product
functional criterion.

1. **The standard module is of Whittaker type**
   (`standardModule_isOfWhittakerType_of_surjective`). Let
   `f : ξ → ρ` be a surjective intertwining map onto a representation `ρ`
   with a nonzero `standardCharacter ψ r` functional.
   - Pulling that functional back along `f` gives a nonzero functional on
     `ξ` (`functionalsComap_ne_zero`).
   - `TemperedLanglandsDatum.universeLift` raises the block carriers of `d`
     to universe `max uF uV`. `universeLiftStandardModuleEquiv` identifies
     the two standard modules, so the lifted standard module also has a
     nonzero functional.
   - The lifted standard module is the normalized product of the twisted
     blocks `ν^(u_i) π_(i,0)`. `hasStandardFunctional_finiteProduct_iff`
     (the Bernstein-Zelevinsky derivative criterion, which needs blocks in
     universe `max uF uV`) then gives every twisted block a nonzero
     functional for its entrywise character.
   - Each twisted block is irreducible (`isIrreducible_twist_iff`) and
     admissible (`IsTempered.isAdmissible` with `isAdmissible_twist_iff`), so
     it is generic.
   - `normalizedProduct_isOfWhittakerType_of_blocks` applies to these blocks
     and makes the lifted standard module of Whittaker type. That lemma
     rewrites the block sizes `B.size i` as `m i + 1` and changes the
     entrywise character to `standardCharacter`
     (`entrywiseCharacter_eq_standardCharacter`). It then combines
     `isOfWhittakerType_of_isGeneric` (which uses the published multiplicity
     one theorem) with `normalizedProductWhittakerType`.
   - `IsOfWhittakerType.of_equiv` moves Whittaker type back to `ξ`.
2. **Equal Whittaker functions**
   (`whittakerSet_eq_of_surjective_of_whittakerType` and its
   inverse-character analogue). Let a source of Whittaker type map onto a
   representation with a nonzero functional `ℓ₂`.
   - Every source functional is a multiple of the pullback of `ℓ₂`
     (`IsOfWhittakerType.eq_smul`).
   - Linearity of `functionalsComap` and `coefficientModel_functionalsComap`
     put each coefficient function of the source among those of the image
     (`exists_coefficientModel_of_surjective`).
   - `whittakerSet_subset_of_surjective` gives the other inclusion.

   For the inverse character, the standard module's inverse Whittaker type
   comes from `isOfWhittakerType_standard_iff_inverse`. The inverse
   functional of the generic quotient comes from
   `isOfInverseWhittakerType_of_isGeneric`.
3. **The L relation sees only Whittaker functions.**
   - `isPairLPolynomial_congr_whittakerSets` proves this for
     `IsPairLPolynomial`. It splits into the unequal-rank case (rewriting
     `unequalRankZetaValues`), the equal-rank case (`equalRankZetaValues`),
     and the case where no polynomial qualifies
     (`not_isPairLPolynomial_of_lt`).
   - `isPadicPairLPolynomial_congr_whittakerSets` passes this through the
     quantifier over quotient measures of `IsPadicPairLPolynomial`.
   - `isPadicSymmetricLPolynomial_congr_whittakerSets` handles both rank
     orders of `IsPadicSymmetricLPolynomial`. It needs four set equalities:
     `ψ` and `ψ⁻¹` Whittaker functions for each member.
4. **Main theorem.**
   - `isOfWhittakerType_of_isGeneric` makes `π` and `σ` of Whittaker type.
   - `symmetricLPolynomialExists` (with carrier universes `max uF uV` and
     `max uF uW`) supplies `P` with `IsPadicSymmetricLPolynomial` for
     `(π, σ)`.
   - Steps 1 and 2 give the four set equalities between the standard modules
     and their quotients. Step 3 transfers the relation to
     `(d.standardModule, e.standardModule)` with the same `P`.

## Remarks

- Only the existence of the surjections and the genericity of `π` and `σ`
  are used. Irreducibility of the quotients (part of `IsLanglandsQuotient`)
  enters only through `IsGeneric`. The proof uses neither the strict
  ordering of the exponents nor the uniqueness of the Langlands datum.
- As a by-product, step 1 proves that a standard module with a generic
  quotient is of Whittaker type. This is the instance of JPSS's (2.3) needed
  here. Neither the genericity of all tempered representations nor (2.3) in
  general is proved.
- Provenance: the helper lemmas are internal. They are derived from the
  published Whittaker-transport, finite-product criterion, multiplicity-one
  and existence modules named above.

## Lean checks

`lean_check` of this module with declaration
`Langlands.RankinSelberg.genericLanglandsQuotientLFactor`: 0 errors, 0
warnings; axioms `propext`, `Classical.choice`, `Quot.sound`.
