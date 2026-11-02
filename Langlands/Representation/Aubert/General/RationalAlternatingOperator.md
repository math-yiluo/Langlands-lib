# The unadjusted operator on the standard rational-point family

Worker 165 constructed this internal specialization of the published general
operator. Its ambient group is exactly `RationalPoint k G.X`. Throughout this
module its topology is explicitly the published `pointTopology`, obtained by
transporting the affine evaluation topology to identity-test rational points.
It takes no arbitrary ambient topology argument.

The base is a topological field `k : Type u`, with an affine group scheme `G`,
a commutative group scheme `T`, a monomorphic homomorphism `i : T.toGrp ⟶ G`
and a cocharacter `ν`. The group is assumed connected reductive, the torus
maximal split and the cocharacter generic. `StandardCocharacterStatement` is
an explicit shared assertion. The derived decomposition from
`RationalParabolicDecomposition` is used for every finite subset of the
literal subtype `SimpleRoot i ν`. No decomposition is supplied as opaque data.

Local compactness, the nonarchimedean group structure and the Hausdorff
property of the rational-point group with this exact topology are separate
typeclass premises. Closedness of each standard parabolic and unipotent
subgroup, continuity of each derived projection, and the property that each
unipotent subgroup is a limit of compact subgroups are also separate premises.
The module proves none of these properties.

`standardParabolicFiniteLength` derives the exactness needed for exact K0
from the existing topological induction and Jacquet theorems. Its remaining
representation-theoretic premises are separately supplied finite-length
preservation for normalized induction and for normalized Jacquet restriction.
These concern smooth complex representations with carrier universe
`max (u + 1) v`. The exact-K0 construction includes its own quotient universe;
it is the existing `FiniteLengthGrothendieckGroup`, not a newly defined class
group.

`standardUnipotent_isUnimodular` applies the existing compact-limit theorem.
Consequently the generic normalized induction in this module has the source
normalization: its half-character on the parabolic is the inflation of the
Levi half-character. This qualification is necessary for the generic adapter.
The Jacquet functor takes the actual unipotent coinvariants and twists by
the inverse half-character.

The explicit `HasRelativeRootSystem i` premise supplies the finite enumeration
through the published `simpleRelativeRootFintype`; splitness is obtained from
the maximal-split-torus premise. This enumerates exactly the actual simple
characters, without an unrelated finite label type or a positive-rank premise.
Neither the root-system assertion nor any Coxeter realization is proved here.

`rationalAlternatingOperator` is literally the existing
`General.alternatingOperator` specialized to these standard point subgroups,
derived decompositions, closedness proofs and proved exactness consequences.
It is the sum over all finite subsets `I` of the actual simple-root subtype
of `(-1)^|I|` times normalized induction after normalized Jacquet restriction.
`rationalAlternatingOperator_ofRepresentation` gives that signed sum on every
actual finite-length representation class. The proof is the published
class formula. `rationalAlternatingOperator_of_isEmpty` specializes the
published empty-index calculation to the single term of sign `+1`. It does
not assert that this term is the identity: endpoint subgroup identifications
remain separate structural assertions.

This is an internal derived construction. Its source convention is the
unadjusted sum already documented and implemented in the imported general
operator. No new literature assertion, Aubert identity, finite-length
preservation theorem or topological realization theorem is claimed. The
ultimate local-field specialization includes positive characteristic; this
construction itself imposes no characteristic restriction and needs no
local-field predicate beyond the explicit premises above.
