# Normal reductive semigroup intersection reduction

`RelativeRoot.NormalReductiveSemigroupPrerequisites` is an internal bundle
of five existing proposition targets at the same arbitrary universe:
actual adjoint-quotient existence, a fixed split torus containing the full
centre, full-centre containment for a normal connected reductive subgroup,
the semigroup fppf image under an adjoint quotient, and an equivariant
retraction onto a normal adjoint subgroup. Defining this conjunction does
not establish any component.

`semigroup_comap_eq_of_normalReductive_quotients` assumes the last four
propositions and supplied actual adjoint quotients of the two groups. Over
an algebraically closed field of arbitrary characteristic, a closed normal
inclusion compatible with the two actions of a split torus then satisfies
the actual semigroup inverse-image equality, provided `0 ∈ A`. Affineness
is explicit so that the intrinsic semigroup subgroup functors are defined.
The supplied adjoint quotients already imply connected reductivity of both
original groups and adjointness of both quotient groups.

The implemented proof derives inclusion of the full source centre in the
inverse image of the full ambient centre from the assumed structural
centre proposition. Closedness of the original inclusion gives monicity.
`IsAdjointQuotient.subgroupHom` constructs the map between the supplied
quotients; its published properties give a commuting square, a closed
normal inclusion and equivariance for the canonical quotient actions.
These are statements on all test schemes, including nonreduced schemes.

The assumed adjoint-image proposition supplies the two actual fppf
semigroup restrictions. The fixed-torus proposition, through
`center_le_semigroupSubgroup_of_fixedCenterContainingTorus`, places both
full centres in their respective semigroup subgroups using `0 ∈ A`.
The published normal-adjoint quotient-square comparison then applies:
equivariant retraction gives comparison on the adjoint groups, and
full-kernel fppf descent pulls it back to the original inclusion. Neither
centre, quotient map nor semigroup restriction is required to be smooth.
No lifts on every original test scheme are assumed.

`semigroup_comap_eq_of_normalReductive` assumes the complete five-part
bundle, chooses the two actual quotients using its existence component,
and applies the preceding theorem. Its conclusion is an equality of
subgroup functors on every test scheme.

This is an internal assembly of the named Library interfaces, rather than
a new source translation. Its mathematical purpose is the reductive
full-centre quotient step in the normal-intersection argument. It proves
no component of the prerequisite bundle and supplies neither the
unipotent-radical reduction nor algebraic-closure descent. Consequently it
does not prove the unrestricted normal-intersection case or the complete
`SemigroupComparisonStatement`.
