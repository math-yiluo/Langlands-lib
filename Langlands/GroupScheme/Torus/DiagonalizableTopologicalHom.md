# Diagonalizable homomorphisms and the topology of the base

Worker 646. Internal infrastructure for multiplicative-type nilpotent lifting.

`homLocus f g` is the union of the open subschemes on which the actual
homomorphism `f : D_X(M) → D_X(N)` is the map induced by `g : N → M`.
The loci are pairwise disjoint. When both character groups are finitely
generated, the published local character-map theorem shows that they cover
the base. Restriction to the entire locus is still the indicated map, by
local equality of actual group-scheme homomorphisms.

`dpull_injective_of_surjective` proves that a surjective map of underlying
base spaces detects equality of split homomorphisms. Around a point, both
homomorphisms are fixed character maps. Their restrictions agree on the
nonempty inverse image of that neighbourhood, so character-map injectivity
identifies them. This proof allows nonreduced schemes and torsion characters.

These are derived constructions and proofs from the Library's
`DiagonalizableIsoLift` and `RelativeDiagonalizableHomLocality`. No
infinitesimal lifting or multiplicative-type equivalence is assumed.

`assembleHom U` glues the character map indexed by `g : N →+ M` on
each open `U g`, assuming that the coproduct of the open inclusions is
an isomorphism onto the base. It uses the actual group-scheme Hom
assembly in `Descent.DisjointComponents.groupHom`. The canonical
diagonalizable base-change comparisons identify each component with
`D_(U g)(M)` and `D_(U g)(N)`. The lemma `dpull_assembleHom` verifies the
prescribed restriction.

For a scheme morphism `b : Y → X` whose underlying map is a
homeomorphism, `imageHomLocus b hb f g` is the image in `X` of the
character-map locus of a homomorphism `f` over `Y`. The images are open
and pairwise disjoint, and for finitely generated character groups they
cover `X`. The instance `imageHomLocus_isIso` establishes the required
coproduct decomposition.

`dpull_bijective_of_isHomeomorph` then proves bijectivity of the actual
split Hom pullback, with its source and target expressed using the
canonical diagonalizable comparisons. To construct a lift, assemble the
maps `D(g)` on these image opens. Restricting back to each original
locus gives `D(g)`, because its inclusion followed by `b` factors through
the corresponding image open. Local equality gives the required global
equality. Injectivity is the earlier surjective-base lemma.

The statements hold over arbitrary schemes in every universe. They
allow torsion in either finitely generated character group, nonreduced
bases and the empty base. Only the topology of `b` is used; no
flatness, field or local-ring hypothesis is imposed. This is a split
Hom result, and supplies neither descent for nonsplit forms nor object
lifting across thickenings. All constructions and proofs are derived
internal infrastructure from the imported local character-map
classification, disjoint-component assembly and pullback coherence.
