# Exactness through the actual Jacquet degree equivalences

This internal module packages the preceding actual homogeneous Jacquet
comparison as a comparison of representations and transfers the existing
concentration conditions through it. It retains an arbitrary prime, supplied
p-adic field and topology, independent field and coefficient universes, rank
zero, and all degrees. No smoothness, finite length, or dimension hypothesis
is needed for the degreewise results.

`jacquetDegreeRepresentationEquiv` equips the canonical
`jacquetDegreeEquiv` with its proved normalized Levi equivariance. Its source
is the actual normalized Jacquet representation of the original degree
product. Its target is the coordinate product of the actual normalized Jacquet
cut terms. The modulus and normalization on both sides are the supplied
actual ones.

The actual normalized Jacquet transition maps intertwine the coordinate Levi
actions. The existing equivariant signed-diagram construction therefore
defines `jacquetDegreeDifferential` as an actual intertwiner with underlying
linear map the signed differential of `jacquetDiagram`.
`jacquetDegreeRepresentationEquiv_differential` packages the already proved
pointwise differential comparison as an equality of actual intertwiners.
It preserves the original exterior insertion signs.

`jacquetDifferential_injective_iff` transports injectivity in both directions
using the inverse of the source degree equivalence and injectivity of the
target degree equivalence. `jacquetDifferential_exact_iff` applies the
standard linear exactness comparison to the commuting squares in consecutive
degrees. The three vertical maps are the genuine degree equivalences, hence
surjective, bijective, and injective as required. The result is equality of
the incoming range with the outgoing kernel on one side if and only if it is
so on the other. `jacquetDegree_subsingleton_iff` transports zero degree
carriers through the same equivalence.

Finally `jacquetConcentratedAt_iff_diagram` rewrites the existing
`JacquetConcentratedAt` condition for any chosen family of block shapes:
injectivity of the initial differential below the surviving degree, middle
exactness strictly below that degree, and zero carriers above it can all be
checked on the actual coordinate Jacquet diagram. The original smooth degree
morphisms have exactly the underlying actual differentials used here.
No condition of exactness at the surviving terminal quotient is added.

The provenance is internal, from the actual degree equivalences and their
commuting differential squares and elementary linear exactness transport.
This module does not establish the geometric graded-piece comparison or
unconditional lower exactness and does not prove signed Aubert effectivity.
