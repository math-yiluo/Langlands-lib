# Ambient character transport of the actual standard integral

Author: Worker 359.

This internal prerequisite for full unitary regularity transports the actual
Levi-normalized standard integral under an ambient smooth complex character.
Its provenance is the Library's character multiplication equivalence for
smooth induction, the projection factorization of a radical-trivial
character, the smooth contragredient twist equivalence, and the actual weak
integral definitions. It introduces no analytic convergence assumption.

Fix a locally compact nonarchimedean group `G`, a semidirect decomposition
`P = M U` with closed `U`, a smooth representation `A` of `M`, and a smooth
character `χ` of `G` trivial on `U`. The inducing representation uses the
positive Haar half modulus on `M` followed by the actual projection
`P → M`. The lemma `leviInflatedInducingRepresentation_characterTwist`
commutes the two scalar actions using the existing projection identity.
The equivalence `leviInductionCharacterTwistEquiv` is multiplication of an
actual induced function by `χ(g)` at every ambient argument `g`; its inverse
multiplies by `χ(g)⁻¹`. It intertwines the ambient twist of the original
induced action with induction from the restricted twist of `A`.

For a target subgroup `U'` on which `χ` is also trivial, the actual integrand
on `(U ∩ U') \ U'` is multiplied by the constant `χ(g)`. No normality is
assumed for the intersection, and the integration measure is unchanged.
An open-kernel twist leaves the underlying set of smooth linear functionals
unchanged, by `smoothContragredientTwistEquiv`. Consequently the weak-integral
relation is unchanged by twisting its testing representation. Complex
homogeneity then proves `hasIntegral_characterTwist_iff`, including scalar
absolute convergence and existence of a representing vector in the original
inducing carrier.

The domain membership equivalence follows by transporting the representing
function and its inverse scalar multiple. Surjectivity of the induced
equivalence gives `domain_eq_top_characterTwist_iff`, so convergence on the
entire source is preserved without being separately assumed for the twisted
representation. The ambient group and representation carrier universes are
independent. No admissibility, irreducibility, quotient invariance, compact
splitting, or unitarity is required.

This module does not yet prove invariance of the canonical rational scalar,
one-coordinate dependence, rank-one factorization, or full unitary regularity.
