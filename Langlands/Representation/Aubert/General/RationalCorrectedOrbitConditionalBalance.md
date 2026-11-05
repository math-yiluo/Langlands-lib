# Conditional character detection for the actual corrected orbit

Authors: Worker 561 and Worker 700.

This derived intermediate specializes the equal-centralizer determinant and Haar
balance to the actual corrected-orbit realization. It does not prove
`RationalCorrectedOrbitSquaredModulusStatement`. The full-character detection
premise remains explicit.

For a `CorrectedOrbitCocharacterRealization r`,
`r.determinantSquareDefect` is the rational character on the represented common
centralizer equal to the determinant on the first actual radical plus the
determinant on the conjugated second actual radical minus twice the determinant
on their scheme-theoretic intersection. The three coordinate systems are
`r.leftRadicalCoordinates`, `r.rightRadicalCoordinates`, and
`r.intersectionCoordinates`, obtained from the actual finite Lie kernels.
Defining the character requires an affine ambient group locally of finite type
over an arbitrary field in universe `u`.

Under the relative-root-system hypothesis, a monomorphic original torus map,
and splitness of the torus,
`characterRestrict_determinantSquareDefect_eq_zero` proves that this character
restricts to zero along `r.torusHom`. It applies
`Dynamic.characterRestrict_centralizingDeterminantSquareDefect_eq_zero` to the
actual represented radicals, the represented literal intersection, the equality
`r.centralizer_eq`, and the factorization `r.torusHom_comp`.
`determinantSquareDefect_eq_zero_of_characterRestrict_injective` upgrades this
restriction to full vanishing only under
`Function.Injective (characterRestrict r.torusHom)`.

Over a nonarchimedean local field, with smooth affine ambient group and the
displayed locally compact, nonarchimedean and Hausdorff canonical point topology,
`squared_modulus_of_characterRestrict_injective` proves the literal identity

`delta_(U_I)(l) * delta_(U_K)(m⁻¹ * l * m) = delta_Z(l)^2`

for every original Levi point `l`, conditional on that same injectivity premise.
Here `Z` is exactly
`CorrectedFiltration.orbitUnipotentIntersection (unipotent i ν I)
(unipotent i ν K) m`. The factors are the existing
`HaarModulus.closedRestrictCharacter` values, and the second is evaluated at
`conjugationEquiv m hK l`. Closedness of the two standard radicals, the two
semidirect decompositions, and the whole-Levi comparison `hK` are explicit
inputs. Closedness and normalization of `Z` use the existing exact lemmas.

The proof supplies the actual radical models, intersection model, original
torus factor and finite coordinates to
`centralizingHaarCharacter_values_square_of_centralizer_eq`. The closedness
arguments come from `r.isClosed_left`, `r.isClosed_right`, and
`r.isClosed_intersection`. Then `r.squared_modulus_of_dynamic_balance` transports
the resulting balance to every original Levi point using its three exact Haar
comparisons. Thus the character formula is attached to the target's literal
moduli and preserves forward conjugation.

No characteristic-zero, split-ambient, root-nonemptiness, target-subset or
minimality premise is introduced. This module does not discharge injectivity,
prove reductivity of the common centralizer, or add a premise to the published
target. Its provenance is internal: the definitions and deductions named above
are the complete mathematical inputs. Worker 700 authored the reused
equal-centralizer determinant and Haar modules; Worker 561 supplied this actual
specialization and its models and Haar comparisons.
