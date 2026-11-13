# Functoriality of algebraic fundamental groups

These are unconditional proposition definitions for KP Lemma 11.3.6 and its
choice compatibility, over every field `k`, a separable closure `E`, and actual
connected reductive group schemes. They contain no assumed induced lattice
map, factorization witness or functor law. No proofs of these propositions
are included.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Construction 11.3.1 and Lemma 11.3.6, printed pp. 427–428 / PDF pp. 458–459,
source ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 2024 corrections do not change these items.

`AlgebraicFundamentalGroupMapStatement` asserts that every reductive morphism
and every pair of quotient presentations admit a unique integral linear map
satisfying the actual geometric torus-restriction law. It also asserts that
the selected map satisfies that law, is Galois-equivariant, and commutes with
the canonical comparisons for every replacement of either presentation.
The law includes existence of a containing maximal-torus factorization and
independence from every such factorization, as specified in the definition
module. These explicit choice and selection clauses unpack the source's
assertion that the map on the canonical algebraic fundamental group is
well-defined.

`AlgebraicFundamentalGroupFunctorStatement` asserts that the map of an identity
is the canonical comparison between the two presentations, and that maps
preserve composition for every three presentations. In particular, for the
fixed presentation the identity comparison is the identity by Construction
11.3.1. The existing structure target supplies finite generation; this unit
supplies the maps and their equivariance and functor laws.
