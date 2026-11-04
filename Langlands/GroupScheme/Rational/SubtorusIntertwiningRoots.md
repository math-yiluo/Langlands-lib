# Dynamic intertwining roots under split-torus restriction

Author: Worker 200.

This internal construction reuses the published same-field root restriction
theorem `Langlands.GroupScheme.mem_roots_comp_iff` from
`Torus/WeightRestriction`, by Worker 1317. It does not reprove the decomposition
of a restricted weight space. Its new comparison concerns the complete
two-sign dynamic intersection under an arbitrary morphism of split tori.

The field has arbitrary universe and characteristic. Let `f : A → T` be any
actual morphism of split tori, and `i : T.toGrp → G` any actual morphism to a
smooth affine group scheme. No monomorphism, reductivity, maximality, Weyl-group
finiteness or injectivity of restriction on characters is required.

`latticePairing_restrict_cocharacterMapInt` identifies the pairing of
`f ≫ beta` with `nu` in `A` with the pairing of `beta` with the actual
postcomposition `cocharacterMapInt f nu` in `T`. The proof is associativity of
composition in the defining endomorphism of the multiplicative group.

For integral cocharacters `nu`, `eta` of `A`,
`intertwiningRelativeRoots_dynamic_restrict` identifies the local dynamic
intersection with the image under actual character restriction of the
ambient dynamic intersection for their postcompositions in `T`.
Both intersections use the dynamic subgroup of the first cocharacter and
the dynamic subgroup of the negative of the second cocharacter.

The proof first applies the published exact dynamic-support formula: the
intersection consists of all actual roots pairing positively with the first
cocharacter and negatively with the second. Given a local root, the published
root restriction theorem supplies an ambient root lifting it. Pairing
naturality transfers both strict signs to that lift. Conversely, a root in
the ambient intersection has positive pairing with the postcomposition of
`nu`. Its restricted character therefore has positive `nu`-pairing, so cannot
be zero. The same root restriction theorem proves local root membership,
and pairing naturality transfers both signs.

`dynamicIntertwiningRootRestriction` sends an actual ambient root in this
intersection to its restricted character with the proved local membership.
Its evaluation rule is definitional. The set-image equality proves
surjectivity by choosing an ambient preimage for each local root. The map
can identify different ambient roots; no injectivity is asserted. Every
actual local root is reached, including multipliable roots. Empty
intersections and rank zero remain allowed.

The provenance is the published split-torus root restriction theorem, the
proved dynamic-support formulas, and associativity of the actual lattice
pairing. The equality concerns these dynamic two-sign supports; it does not
assert that arbitrary images commute with intersections, or establish a
restriction formula for arbitrary subgroup tangent supports. It identifies
no unspecified parabolic radical or common Levi and makes no analytic claim.
