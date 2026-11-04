# Semigroup comparison from five structural prerequisites

Worker 1372. This is an internal consequence of the existing six-input
comparison assembly and the conditional descent of full-centre containment.

`SemigroupComparisonPrerequisites.{u}` is the conjunction of adjoint quotient
existence, a fixed centre-containing split torus, the adjoint semigroup image
proposition, the normal adjoint equivariant retraction proposition, and
solvable fixed-containment connectedness. It asserts none of these five
components without a supplied proof.

`SemigroupComparisonPrerequisites.normalReductive` derives the former
five-component `NormalReductiveSemigroupPrerequisites` from the first four
retained inputs. Its full-centre containment component follows from the
fixed-torus input by `normalReductiveCenter_of_fixedCenterContainingTorus`,
which works over every field.

`semigroupComparison_of_fivePrerequisites` applies the existing six-input
comparison assembly to this derived bundle and the supplied solvable
connectedness component. That assembly also derives the radical-intersection
input from the fixed-torus component. Its conclusion is the exact existing
`SemigroupComparisonStatement.{u}`: all-test equivariant functoriality, an
actual smooth surjective morphism between arbitrary semigroup subgroup
representatives, and intersection equality in each of the three alternatives
(zero excluded, subgroup solvable, or subgroup normal). Every original field,
universe, action, subgroup and representative hypothesis is retained.

The five inputs remain explicit unproved premises of this module. This
conditional deduction does not complete the unconditional comparison target.
