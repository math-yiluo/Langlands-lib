# Local character restrictions for diagonalizable homomorphisms

This internal construction converts the all-test idempotent restriction
certificate for diagonalizable homomorphisms into an actual open cover of
the base. It is derived from the preceding grouplike monomial-locus
construction, the Library's residue-field and basic-open descriptions,
and the full point model of base change.

Let `R` be any commutative ring and
`f : D_R(Γ) ⟶ D_R(Λ)` an actual homomorphism, with `Λ` finitely
generated. For every point of `Spec R`, `exists_open_restriction`
provides an open neighborhood and a homomorphism `p : Λ →+ Γ`
such that the two actual homomorphisms `f` and restriction along `p`
become equal after base change to that neighborhood.

The definition `restrictionCover f` chooses these neighborhoods as an
open cover of `Spec R`. The definition `restrictionCharacterMap` records
the character map on each member, and `restrictionCover_map_eq` retains
the equality of the actual base-changed group-scheme maps.
No connectedness, reducedness, or nonemptiness of `Spec R` is assumed,
and neither character group is required to be torsion-free.

The proof specializes the universal grouplike character family to the
residue field at the selected prime. The resulting idempotent `e` maps
to one in that field, so its basic open contains the selected point.
For every test over this basic open, containment in the basic open
means that the pullback of the idempotent is one. The existing all-test
restriction certificate then identifies the maps on every point group.
The injective base-change point equivalence proves equality of the
actual base-changed group-scheme homomorphisms.

Surjectivity of the chosen character map for closed subgroup inclusions,
and transport to relative diagonalizable models, are separate obligations.
