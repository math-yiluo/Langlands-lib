# Arithmetic pullback on actual automorphic and cuspidal forms

This module is an internal construction. It extends the published
arithmetic-transport chain (`AmbientArithmeticTransport`,
`SmoothArithmeticTransport`, `GrowthArithmeticTransport`,
`CenterFiniteArithmeticTransport`, `ConstantTermArithmeticTransport`) from
general smooth functions to the project's automorphic and cuspidal form
spaces. It replaces the CM involution of the published `AutomorphicCMTransport`
and `CuspidalCMTransport` by an arbitrary field isomorphism. No new object from
the original literature is identified here.

Throughout, `K : Type uK`, `L : Type uL` and `M : Type uM` are number fields in
independent universes and `e : K ≃+* L` is a ring isomorphism. The rank `n` is
any natural number, including zero. Coefficients are complex, and pullback
does not change values. The arithmetic pullback `arithmeticComap n e` sends a
function `f` on `GL_n(𝔸_L)` to `f ∘ adelicEquiv n e` on `GL_n(𝔸_K)`, where
`adelicEquiv n e` applies `e` entrywise.

## The four automorphic conditions

`IsAutomorphicForm` (module `Forms`) has four conditions:

1. existence of a compact open finite level;
2. finiteness under the standard compact subgroup `standardInfiniteCompact`;
3. finiteness under the centre of the enveloping algebra;
4. slice-wise polynomial growth.

- `isStandardInfiniteFinite_arithmeticComap_iff`: pullback preserves and
  reflects condition (2). The published `isInfiniteFinite_arithmeticComap_iff`
  reduces it to the preimage of `standardInfiniteCompact L n`.
  `ArchimedeanCompactTransport.comap_infiniteEquiv_standardInfiniteCompact`
  identifies that preimage with `standardInfiniteCompact K n`.
- `isAutomorphicForm_smoothEquiv_iff`: all four conditions are preserved and
  reflected. The other three use the published
  `hasFiniteLevel_arithmeticComap_iff`, `isCenterFinite_smoothEquiv_iff` and
  `arithmeticComap_hasPolynomialGrowth_iff`.
- `finiteSmoothEquiv_mem_automorphic_iff`: the same statement on the
  common-stabilizer smooth space that carries `automorphicSubrepresentation`.

## Equivalences of form spaces

All equivalences below are restrictions of the published continuous linear
equivalence `finiteSmoothEquiv n e`. Their topologies are inherited from the
compact-open topology on continuous functions. Each `…_val` lemma gives the
underlying function.

- `AutomorphicForms.arithmeticEquiv n e : AutomorphicForms L n ≃L[ℂ] AutomorphicForms K n`.
  - `toContinuous_arithmeticEquiv` and `evaluate_arithmeticEquiv` give the
    function `x ↦ f (adelicEquiv n e x)`.
  - `arithmeticEquiv_refl`, `arithmeticEquiv_trans` (contravariant composition
    through `M`) and `arithmeticEquiv_symm` (the inverse is pullback along
    `e.symm`) give the identity, composition and inverse laws.
  - `arithmeticEquiv_finiteRightAction`: translation by `finiteEquiv n e d` on
    `L` becomes translation by `d` on `K`.
  - `arithmeticEquiv_envelopingAction`: the differential action of
    `envelopingEquiv n e u` becomes that of `u`.
  - `arithmeticEquiv_mem_centralCharacter_iff`: a form has central character
    `χ` exactly when its pullback has central character
    `HeckeCharacter.comap e χ`.
  - `arithmeticEquiv_mem_level_iff`: a form is fixed by a finite level `U`
    exactly when its pullback is fixed by the preimage level.
- `CentralCharacterAutomorphicForms.arithmeticEquiv n e χ` sends forms with
  central character `χ` to forms with central character
  `HeckeCharacter.comap e χ`. It intertwines finite translation in the same way.

With the compactness parameters `[CompactSpace (AdeleQuotient K)]` and
`[CompactSpace (AdeleQuotient L)]` explicit:

- `AutomorphicForms.arithmeticEquiv_mem_cuspidal_iff`: the published
  constant-term cusp condition is preserved and reflected
  (`isCuspidal_arithmeticComap_iff`).
- `AutomorphicForms.arithmeticEquiv_mem_centralCharacterCuspidal_iff`: the same
  for the cusp condition together with a central character.
- `CuspidalAutomorphicForms.arithmeticEquiv` and
  `CentralCharacterCuspidalForms.arithmeticEquiv`: the restricted equivalences
  of cusp-form spaces. They have evaluation and finite-translation lemmas.

The private helper `map_arithmeticEquiv_eq` turns a membership equivalence into
equality of image submodules. `ofSubmodules` needs this equality.

## Scope

This module concerns spaces of functions only. Automorphic operator
realizations, their irreducibility and their classes are treated in
`OperatorArithmeticTransport` and `OperatorArithmeticTransportClasses`. No
statement about automorphic representations occurring in these spaces,
multiplicity or local components is made here.
