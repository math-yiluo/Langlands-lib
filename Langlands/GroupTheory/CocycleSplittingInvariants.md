# Invariants and the norm of the cocycle splitting module

For a finite group `G : Type u` acting on a commutative multiplicative group
`A : Type u`, and a normalized two-cocycle `c`, consider the actual splitting
module with carrier `Additive A × Ideal G` over `Scalars = ULift.{u} ℤ`.

A translation-invariant augmentation vector has the same value at every
coordinate. Its coordinate sum is therefore `card(G)` times its value at
the identity. The sum is zero, while `card(G)` is nonzero in the lifted
integers because `G` is nonempty. This forces the vector to vanish.
`ideal_invariant_eq_zero` proves this directly in the actual augmentation
ideal.

For an invariant vector in the splitting module, its second coordinate is
invariant in the augmentation ideal and hence zero. The first coordinate
is then invariant under the original coefficient action, since the twist
vanishes on zero. Thus `splittingInvariantsEquiv` is a linear equivalence
from splitting invariants to coefficient invariants. It takes the first
coordinate, and its inverse is the original coefficient inclusion
`a ↦ (a,0)`.

`splittingNorm` composes the actual norm on splitting coinvariants with
this equivalence. On the class of a vector `x`, its underlying coefficient
is the first coordinate of the group norm of `x`.
`splittingNorm_bijective` assumes that integral cup by `cohomologyClass c`
is bijective in every integer Tate degree. The established
`splitting_tate_isZero` gives vanishing of the splitting module in degrees
minus one and zero. `coinvariantNorm_bijective` then gives bijectivity of
the actual coinvariant norm, and composing with the invariant equivalence
proves the claim.

The provenance is internal, from the displayed coordinate actions,
torsion-freeness of the lifted integers, and the previously proved
splitting-class and norm results. There is no transfer comparison in
this unit. The coefficient group and its action remain the original ones
throughout.
