# Fundamental characters and the D4 relation on central subgroup schemes

This is a derived internal application of the imported fundamental-weight
construction and D4 lattice identity to the actual characters of group schemes.
It imposes no ground-field or residue-characteristic restriction.

The helper `root_comp_eq_zero_of_isCentral` takes an actual root of a torus
homomorphism into an affine, locally finite type field group and an actual
homomorphism from a commutative group scheme into that torus. If their composite
is central, the root restricts to the zero character of the source. The source
need not be smooth, reduced, affine, or itself a torus.

The proof uses the imported result that an actual root evaluates to one on
central points over every affine test scheme. It covers an arbitrary test
scheme by its affine opens, applies that result on each open, and uses equality
of scheme morphisms on the cover. The conclusion is equality of actual group
scheme homomorphisms, so it applies to every test scheme, including nonreduced
ones.

For an actual `TitsIndexData G` of a simply connected group,
`absoluteFundamentalCharacter` is the integral fundamental weight viewed as a
character of the split absolute torus over the separable closure. The integral
coroot-spanning hypothesis is supplied by the imported
`pinning_corootSpan_eq_top` theorem. This character is not asserted to descend
to the ground field.

The definition `centralFundamentalCharacter` restricts that actual character
along a supplied homomorphism into the split absolute torus. The definition
itself does not assert centrality. Under centrality of the composite into the
absolute group, and a numbering preserving every Cartan pairing with
`CartanMatrix.D 4`, the theorem
`centralFundamentalCharacter_D4_leaf_sum_eq_zero` proves that the characters
at vertices `0`, `2`, and `3` sum to zero. Vertex `1` is the central vertex.
The proof pulls back the imported identity

`ω₀ + ω₂ + ω₃ = 2α₀ + 3α₁ + 2α₂ + 2α₃`

and applies the preceding root restriction theorem to all four roots.

All of these are internal deductions from the imported actual interfaces. This
unit does not construct a centre, its inclusion in the torus, Tits algebras,
their comparison with anisotropic-kernel factors, or Brauer corestriction. It
does not prove a local D4 exclusion or the rank-one Tits-index enumeration.
