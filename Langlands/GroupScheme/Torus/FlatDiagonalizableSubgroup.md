# Flat closed subgroups of diagonalizable groups over integral domains

This derived internal development extends the Library's field-level
closed-subgroup presentation argument to a flat subgroup over an integral
domain. It supplies actual Hopf-coordinate and group-scheme constructions.
It does not prove the arbitrary-base fibrewise central-isogeny criterion.

## Statements and constructions

Let `R` be a commutative ring in universe `u`, let `Λ` be an abelian group
in the same universe, and let `H` be a group scheme over `Spec R` whose total
scheme is affine. Given a homomorphism `i : H ⟶ D_R(Λ)`,
`subgroupCoordinateMap i` is its actual contravariant Hopf-coordinate map,
transported along the published affine-coordinate and diagonalizable
relative-spectrum isomorphisms. If `i` is a closed subgroup inclusion, this
map is surjective.

`subgroupCharacterMap i` sends each element of `Λ` to the group-like
coordinate obtained by restricting its monomial to `H`. Its target is the
full additive group underlying `GroupLike R (AffineCoordinates.hopfAlgebra H)`.
For every coefficient ring, the images of the ambient group-like coordinates
span the subgroup coordinate algebra; therefore all its group-like elements
span it as well. Flatness of `H` over `Spec R` implies flatness of its actual
Hopf-coordinate algebra as an `R`-module.

Now assume that `R` is an integral domain and that `H` is flat over it.
The restriction map `subgroupCharacterMap i` is surjective for every closed
subgroup inclusion `i`. The definition `flatClosedSubgroupIso i hi` constructs
an actual group-scheme isomorphism

`H ≅ D_R(Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))`.

This construction does not require finite generation of `Λ`. It keeps the
entire group-like character group, including its torsion, and compares the
actual group schemes rather than only their field-valued points.

If `Λ` is finitely generated, its surjection onto this full subgroup character
group proves that the latter is finitely generated too. Comparison with the
published split model over `Spec ℤ` then proves
`RelativeMultiplicativeType.IsDiagonalizable H`. If additionally the structure
map of `H` is locally quasi-finite, `isFinite_of_flat_closedSubgroup` proves
that structure map finite, using the relative multiplicative-type finiteness
theorem.

## Implemented proof

Closedness makes the coordinate map surjective by the existing
`surjective_of_isClosedSubgroup_hopfSpec`. The monomial group-like coordinates
span the ambient group algebra. Mapping that span through the surjective
coordinate map yields the full coordinate algebra of `H`.

The flatness bridge transports the structure map through
`AffineCoordinates.hopfSpecIso`, identifies it with the spectrum of the
coordinate algebra map, and applies `Flat.SpecMap_iff` and
`RingHom.flat_algebraMap_iff`. Over a domain, flatness supplies the
torsion-freeness required for linear independence of group-like elements.
A spanning subset of group-like elements consequently contains every such
element: an omitted element would lie in the span of a linearly independent
family with itself adjoined. Every ambient group-like element over the domain
is a monomial, which proves surjectivity of the character map.

`Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike` reconstructs the actual
coordinate bialgebra from all its group-like elements. Converting the
multiplicative indexing group to its additive version and applying
`AffineCoordinates.isoOfBialgEquiv` gives the displayed group-scheme
isomorphism. The finite-generation and relative diagonalizability conclusions
use this same isomorphism, and local quasi-finiteness implies finiteness by
`RelativeMultiplicativeType.IsDiagonalizable.isFinite`.

## Provenance and scope

The construction is derived from the Library's
`ClosedSubgroupPresentationProof`, `GroupLikeReconstruction`, affine Hopf
coordinates and actual diagonalizable base-change isomorphisms, together with
Mathlib's flat-module torsion-freeness theorem. These existing constructions
justify the definitions; no new source-level convention or unproved
structural statement is assumed.

The integral-domain hypothesis applies to reconstruction, character
surjectivity and the resulting diagonalizability and finiteness theorems.
The coordinate-map, spanning and flatness lemmas have the weaker assumptions
stated above. The closed-subgroup theorem over arbitrary nonreduced bases,
and global centrality of the kernel in the host criterion, remain open.
