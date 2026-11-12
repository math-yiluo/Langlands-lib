# Conjugate-inverse Hecke characters of CM fields are unitary

Author: Worker 5134. Module `Langlands.Global.HeckeConjugateInverseUnitary`,
namespace `Langlands.Global.HeckeConjugateInverse`. Universe `u` (the field
`K`).

Setting: `K` is a CM number field. `c = IsCMField.complexConj K` is its complex
conjugation, acting on ideles by `ideleEquiv c` and on idele classes by
`ideleClassComplexConj`. `IdeleAbsoluteValue.full K` is the normalized idelic
absolute value `Ideles K →ₜ* ℝ≥0ˣ`. Harris's condition
`Harris.IsConjugateInverse χ` (Harris 1998, Proposition 4.8: `ξ = ξ⁻¹ ∘ c`)
says `χ (c y) = (χ y)⁻¹` for every idele class `y`.

The result is the standard observation that such a character is unitary: its
absolute value is a power of the idelic norm, and the norm is invariant under
`c`. Harris's hypothesis gives `ξ = ξ⁻¹ ∘ c`. Unitarity of the attached Weil
representation is needed when Henniart (2000, §3.4) uses the pairs
`(S(X), Π(X))` as unitary generators.

## Definition: `absCharacter`

For a Hecke character `χ : IdeleClasses K →ₜ* ℂˣ`, `absCharacter χ` is the
continuous character `x ↦ ‖χ (class of x)‖` of the ideles, with values in
`ℝ≥0ˣ`. It is built with `nnnormHom` and `Units.map`. Its values are given by
`coe_absCharacter`.

## Results

- `ideleEquiv_complexConj_positiveReal`: `c` fixes the positive real scalar
  ideles `PositiveRealIdeles.full K a`. These are a positive real number at
  every archimedean place and `1` at every finite place.
- `full_ideleEquiv_complexConj`: `full K (c x) = full K x` for every idele `x`.
- `isUnitary_of_isConjugateInverse`: if `Harris.IsConjugateInverse χ`, then
  `χ.IsUnitary`, that is `‖χ y‖ = 1` for every idele class `y`.

## Proofs

`ideleEquiv_complexConj_positiveReal`. At an archimedean place `p`, the
coordinate of `c x` is the complex conjugate of the coordinate of `x`, read
through `extensionEmbedding p` (Library `ideleComplexConj_infinite_coordinate`).
The conjugate of a real number is itself. At the finite places the idele is `1`,
which the ring isomorphism `finiteAdeleEquiv c` fixes.

`full_ideleEquiv_complexConj`. The character `full K ∘ (ideleEquiv c)` is trivial
on principal ideles (`ideleEquiv_diagonal` and the product formula
`full_diagonalUnits`). By the previous lemma it agrees with `full K` on positive
real scalar ideles. Such characters are equal (Library
`IdeleAbsoluteValue.eq_of_positiveRealIdeles`).

`isUnitary_of_isConjugateInverse`. Let `y` be the class of an idele `x` and
put `x' = c x`. The character `absCharacter χ` is trivial on principal ideles.
`x' x⁻¹` has normalized absolute value `1` by `full_ideleEquiv_complexConj`. So
`absCharacter χ (x' x⁻¹) = 1` (Library
`IdeleAbsoluteValue.apply_eq_one_of_full_eq_one`, which uses compactness of the
norm-one idele classes), and `‖χ (c y)‖ = ‖χ y‖`. Harris's condition gives
`‖χ (c y)‖ = ‖χ y‖⁻¹`. Hence `r = ‖χ y‖ > 0` satisfies `r * r = 1`, so `r = 1`.
