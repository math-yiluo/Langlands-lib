# Divisibility of irreducible complex representation degrees

`Langlands.IrreducibleDegreeDivisibilityStatement` says that for every finite
 group `G` and every finite-dimensional irreducible complex representation
`ρ` on `V`, the complex dimension `Module.finrank ℂ V` divides the group
order `Nat.card G`. The group and carrier universes are independent.

**Source.** J.-P. Serre, *Linear Representations of Finite Groups* (1977),
§6.5, Corollary 2 to Proposition 16, printed p. 52 (PDF p. 60), registered
as `serre-1977-linear-representations`. This is the divisibility by the
full group order, not the stronger divisibility by the index of the
center from Proposition 17. It provides the degree input for wild
inertia: an irreducible representation of a finite `p`-group has
`p`-power dimension. This module does not prove the statement or assert
any comparison of characters under tame restriction.
