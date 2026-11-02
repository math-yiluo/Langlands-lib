# Stable submodules and restriction of coactions

Author: Worker 148.

This internal algebraic unit uses the published `GroupoidCoaction`, `IsHom`,
flat-test `IsOneCocycle`, and `OneCohomologyVanishes` predicates unchanged.
The commutative rings B and C have arbitrary universe u, the B-module M has
independent universe v, and the directed index type has arbitrary universe w.
The given `Algebra B C` is the source structure; t is the separate target map.

`IsStableSubmodule θ N` means that θ(m) lies in the image of
C tensor_B N → C tensor_B M for every m in the B-submodule N.
With C flat over B, tensoring the subtype map is injective. The linear
equivalence onto its image has an inverse, which pulls θ back to the
t-semilinear map `submoduleSemilinearMap`. Its composite with tensor inclusion
is θ restricted to N.

For a `RingEtaleEquivalenceRelation t`, source étaleness supplies this
flatness. The published `ofInjective` constructor then gives the restriction
coaction `submodule`; its subtype map is equivariant. Conversely, any
equivariant coaction on N supplies a preimage of each θ(m), proving
`isStableSubmodule_iff_exists_coaction`. This asserts existence, without
adding a separate uniqueness claim.

The quotient construction needs only stability. The composite of θ with
C tensor_B (M → M/N) kills N: lift θ(m) through C tensor_B N, then use that
the quotient map composed with subtype is zero. `Submodule.liftQ` therefore
defines `submoduleQuotientSemilinearMap`, and the published `ofSurjective`
constructor supplies its coaction laws. The quotient map is equivariant.
This is the same quotient-by-an-image mechanism used in the published
cokernel construction, written with N itself to avoid transporting quotient
module instances across an equality of submodules.

`exists_lTensor_subtype_of_directed` proves that every element of C tensor_B M
comes from C tensor_B F(i) when F is directed by inclusion and every m in M
belongs to some F(i). Tensor induction handles a pure tensor using the cover
condition and handles addition by moving both lifts to an upper member.
This lemma needs no flatness or coaction.

`oneCohomologyVanishes_of_directed_submodules` additionally assumes that
every F(i) is stable and that its restriction coaction has
`OneCohomologyVanishes`. Lift a cocycle into one member using the preceding
tensor lemma. The published injection-reflection theorem shows that the
lift is a cocycle; its proof uses flatness of the test algebras already
quantified in `IsOneCocycle`. Vanishing in that member gives a primitive,
whose subtype image is a primitive in M by coboundary naturality.

The provenance is internal: the constructions and proofs follow directly
from tensor exactness for injections, quotient module universal properties,
and the published coaction and cocycle formulas. No geometric acyclicity,
existence of a directed cover by finite stable submodules, or Noetherian
devissage is asserted here.
