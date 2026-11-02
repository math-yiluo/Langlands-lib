# Topological group properties of actual affine group-scheme points

This statement unit records group consequences of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Proposition 2.1
and the following paragraph, printed page 2. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The declarations are unproved Prop-valued statement definitions.

The coefficient ring `R` and value algebra `S` are arbitrary commutative rings
in a common arbitrary universe. Only `S` has a topology. A group scheme is the
existing `Langlands.GroupScheme (Spec (CommRingCat.of R))`, an actual group
object in the category of schemes over the specified base. Its point carrier
is the existing `RingPoint R G.X S`: actual morphisms from `Spec S` to its
underlying relative scheme. Its group law is the existing group-object law on
this Hom set. Its topology is the published topology induced by the
global-section algebra-map equivalence and point evaluations. Neither law
nor topology is supplied through an assumed package.

`AffineGroupTopologicalProperty` states that these points form a topological
group when `S` is a topological ring and `G` is affine and locally of finite
type over `Spec R`. Here local finite type gives finite type because the
structure morphism is between affine schemes. This is exactly the
group-object consequence of functoriality and product compatibility noted
immediately after Proposition 2.1. It assumes no separatedness beyond
affineness, no field or local-ring condition, and no topology on `R`.

`AffineGroupFunctorialProperty` states that each actual group-scheme
homomorphism induces a continuous point map, and each actual group-scheme
isomorphism induces a homeomorphism. The maps are postcomposition by the
actual underlying relative morphisms. The isomorphism's inverse is induced
by its actual inverse morphism. The group structures already make these
maps multiplicative. This is a derived specialization of functoriality, not
an additional geometric assertion about the existence of any particular
homomorphism, projection or conjugating representative.

`AffineGroupClosedImmersionProperty` states that an actual closed immersion
of such group schemes induces an embedding of point spaces, and a closed
embedding if `S` is Hausdorff. Thus the topology on the domain agrees with
the subspace topology on its image. This is the group specialization of
the closed-immersion assertions in Proposition 2.1. The topological-ring
hypothesis is retained in this finite-type group interface; the separate
arbitrary-affine mapping target has broader scope.

`AffineGroupLocalCompactnessProperty` keeps Hausdorffness and local
compactness distinct. Hausdorff `S` gives Hausdorff points of every affine
group scheme, without finite type or continuity of ring operations.
A Hausdorff locally compact topological ring `S` gives locally compact
points when the affine group scheme is locally of finite type. The first
clause's extension beyond the source's finite-type scope follows from the
published evaluation embedding into the full product of copies of `S`.
The second is the group specialization of Proposition 2.1's local
compactness assertion.

`AffineGroupPointProperties` combines these four targets, quantifying the
topological-ring and separation hypotheses only in the branches that use
them. The relative formulation is derived: the source is recovered by
taking `S = R`. Coefficients in `S` are constant evaluation functions, so no
topology on `R` or continuity of its structure map is required.

This unit does not construct reductive groups or their parabolic, Levi or
unipotent subgroup schemes. It does not assert second countability, a
nonarchimedean group structure or compact open subgroup bases, nor compare
the point topology of an actual general linear group with a matrix
topology. Those specializations and the remainder of the five-section
Conrad program remain separate obligations.
