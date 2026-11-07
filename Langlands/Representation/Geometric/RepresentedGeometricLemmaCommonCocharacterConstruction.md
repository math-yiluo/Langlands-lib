# Actual geometric-lemma data from common-torus cocharacters

This internal construction supplies an actual `GeometricLemmaIntersectionDatum`
for two prescribed represented parabolic triples and a prescribed rational
point `z`. The input is a common ambient maximal split torus with two
cocharacters. On every relative test scheme, the first cocharacter realizes
the original target triple `(Q,L,U)` and the second realizes the original
source triple `(P,M,N)` conjugated by `z⁻¹`. The six dynamic equalities are
explicit inputs.

`geometricLemmaIntersectionDatumOfCommonCocharacters` applies
`commonCocharacterLeviIntersection` inside `M` and `L`, using both original
closed Levi inclusions into the same ambient group in the target frame.
This constructs the actual parabolics, rational Levis, full geometric
unipotent radicals and their multiplication isomorphisms. Transporting the
source intersection by the original inner automorphism `Int(z)` gives its
three required ambient intersection identities. The target intersection
already has the required orientation.

The two constructed common Levis represent the same subgroup functor after
this transport. Uniqueness of representing objects supplies the algebraic
isomorphism `φ`; its ambient composite is exactly the original conjugation by
`z`. The rational-point maps of `φ` and its inverse give the required group
homeomorphism with the canonical Levi point topologies. The common torus is
the supplied torus, factored through the constructed source common Levi. Its
ambient map is the supplied map followed by `Int(z)`, so it remains maximal
split.

The provenance is internal. The single-intersection construction uses the
published dynamic structural proofs. The isomorphism and point-topology
assembly follows `RepresentedGeometricLemmaGeometryReduction`, now applied
to those constructed intersections. There is no supplied
Levi-intersection-structure proposition or universal parabolic-dynamic
proposition. Choosing the two common-torus cocharacters for arbitrary
parabolic triples, proving finite rational double cosets and constructing a
representation-theoretic finite filtration remain separate obligations.
