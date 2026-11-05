# Adelic positive-torus compatibility from supplied local Levi compacts

Author: Worker 112.

`Langlands.Global.AdelicSiegelFactors.AdelicPositiveTorusCompatibilityStatement`
is a proposition-valued definition of a universal implication. Its conclusion
is the existing `IsPositiveTorusCompatible` predicate on the actual adelic
group. This file states the implication; its proof is a separate obligation.

The field `F : Type u` is an arbitrary number field, with unrestricted universe
parameter `u`. The ambient `G` is a group scheme over `Spec F` whose structure
morphism is affine. The commutative group schemes `T₀` and `T` have supplied
maps `j : T₀ ⟶ T` and `i : T.toGrp ⟶ G`, and `ν` belongs to the cocharacter
lattice of `T`. The source `T₀` is assumed split, including split rank zero.
The other algebraic premise is
`standardLevi i ν ∅ = torusCentralizer i`, as an equality of subgroup functors
on all test schemes. No restriction of `F` to a subfield of the real numbers
is made.

The quantification is over every adelic subgroup `K` and every supplied family
`Karch v` of subgroups of the actual completion-point groups at the infinite
places. Each `Karch v` must satisfy the unchanged
`InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact` predicate for
the canonical standard parabolic `Standard.parabolicScheme i ν ∅` and Levi
`Standard.leviScheme i ν ∅`, with their existing inclusion maps. This local
predicate includes maximal compactness, local Iwasawa coverage, equality of
the parabolic and Levi intersections with the compact subgroup, and maximal
compactness of its pullback to the Levi. Each infinite-place projection of
every element of `K` must lie in the corresponding `Karch v`.

The conclusion says that every `k ∈ K` in the image of the actual adelic
points of the canonical parabolic commutes with `positiveMap F G T i T₀ j a`
for every `a : PositiveRealTorus.intrinsicSubgroup F T₀`. There is no
finite-place premise: the intended proof uses the identity finite components
of the actual positive factor. Compactness or maximality of `K` itself is
not a premise or conclusion.

This is an internal compatibility statement joining the Library's intrinsic
positive subgroup, actual local projections, all-test torus centralizer and
canonical Levi representatives. It records the precise implication needed
to use supplied archimedean Levi-compatible compacts in the existing adelic
Siegel construction. It is not attributed to a separate external theorem.
The intended proof compares products at every place, uses the supplied
parabolic/compact intersection property at infinity, and uses split-torus
coordinates at finite places.

The proof development must retain the specialization to an existing
`IsSiegelAlgebraicSetup` and to the actual
`CoordinateCompactAssembly.coordinateSubgroup`. The setup supplies the split
source and the all-test Levi equality; the coordinate subgroup supplies
projection containment. These are prospective consequences, not proved
assertions of this statement file.

All existence and global reduction obligations remain. This statement
constructs neither a Siegel algebraic setup nor local compacts, and asserts
no global Iwasawa coverage, Siegel coverage, finite volume or unimodularity.
It makes no comparison of a maximal `F`-split centre with the greatest
`ℚ`-split centre after restriction of scalars.
