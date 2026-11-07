# The cocycle class of the splitting module

Let `G : Type u` be a finite group, let `A : Type u` be a commutative
multiplicative group with a distributive `G`-action, and let `c` be an actual
normalized two-cocycle with values in `A`. All representations use
`Scalars = ULift.{u} ℤ`. This internal unit computes the class of the actual
splitting sequence and applies the scalar double-boundary theorem.

The regular module, augmentation ideal and twisted splitting module are those
of `CocycleSplittingModule` and `CocycleSplittingExtension`. With `delta(h)`
the coordinate vector at `h`, `augmentationCocycle g` is
`e_g = delta(g⁻¹) - delta(1)`. Its coordinate sum is zero.
The explicit right translation on the regular module gives
`g · delta(h) = delta(h g⁻¹)` and hence
`g · e_h = e_(gh) - e_g`. This proves the one-cocycle relation in the
actual augmentation ideal, with no quotient or replacement action.

The correction term of the splitting action satisfies
`twist c g delta(h) = ofMul(c(g,h⁻¹))`. Normalization therefore gives
`twist c g e_h = ofMul(c(g,h))`.

`augmentationOneCocycle` packages the function `g ↦ e_g` in Mathlib's
one-cocycle module. The proof uses the inclusion of the augmentation ideal:
composing that inclusion with this function gives the ordinary differential
of `delta(1)`. Since augmentation sends `delta(1)` to one,
Mathlib's `groupCohomology.δ₀_apply` identifies the connecting map of the
augmentation sequence on invariant one with the class of this one-cocycle.

Lift the one-cocycle to the splitting module by `g ↦ (0,e_g)`.
Its ordinary one-cochain differential has first coordinate
`ofMul(c(g,h))` by the twist identity and second coordinate zero by
the one-cocycle relation. Thus `groupCohomology.δ₁_apply` identifies
the next connecting map with `cohomologyClass c`.
`ordinary_doubleBoundary` states this equality of actual ordinary
cohomology classes.

`scalarDoubleBoundaryClass_eq` identifies this result with the
`scalarDoubleBoundaryClass` from `ScalarCupBoundary`. Its proof uses
`ordinaryToTate_delta` for the two exact sequences and
`ordinaryToTate_zero_invariant` at invariant one. The positive-degree
ordinary-to-Tate comparison is inverse to the canonical Tate-to-ordinary
isomorphism, so cancelling that isomorphism proves equality with
`cohomologyClass c`. No sign change is introduced.

Finally, `splitting_tate_isZero` assumes that cup by `cohomologyClass c`
is bijective from the integral trivial representation in every integer
Tate degree. The splitting and augmentation sequences have the scalar
splittings already constructed in `CocycleSplittingExtension`, and the
regular module is Tate acyclic. Substitution of the computed class into
`scalarDoubleBoundary_middle_isZero` therefore proves Tate acyclicity
of the actual splitting representation in every integer degree.

The provenance is internal: the definitions and calculations above derive
from the displayed coordinate actions and Mathlib's ordinary connecting-map
formulas, followed by the Library's proved ordinary-to-Tate comparison
and scalar cup theorem. The unit introduces no new arithmetic hypothesis or
source assertion. Identifying splitting-module coinvariants with an
extension's abelianization, comparing its norm with transfer and applying
these results to relative global Weil groups remain separate obligations.
