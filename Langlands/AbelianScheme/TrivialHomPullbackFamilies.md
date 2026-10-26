# Families with trivial homomorphism pullback

For a homomorphism `f : A ⟶ B` of actual abelian schemes and a scheme `T` over
`S`, `HasTrivialHomPullback f T L` says that the actual module pullback of the
actual line bundle `L` on `T ×_S B` along `f_T` is isomorphic to the structure
module on `T ×_S A`. It is a proposition expressing existence of a concrete
trivialization; neither a scalar nor a character occurs as input.

`homFamilyModulePullbackIso` constructs the canonical comparison between the
two orders of pullback in the actual commutative square for `f_T` and a change
of test scheme. It uses the actual pullback-composition isomorphisms and the
naturality equality of `homFamilySpaceMap`. This proves that the condition is
preserved by change of test scheme. The condition is also preserved by an
actual line-bundle isomorphism, and the trivial line bundle satisfies it.

`TrivialHomPullbackFamily` is the full subcategory of line bundles with this
property. No trivialization is chosen in this category. The quotient
`TrivialHomPullbackClasses` identifies its objects by isomorphism of their
underlying line bundles. `trivialHomPullbackClassOf_eq_of_iso` records this
identification explicitly. The restriction functor is the usual actual
pullback of line bundles, with the proof of preservation just described.

`trivialHomPullbackClassPresheaf` is the presheaf of these classes. Identity
and composition of restriction follow from the existing line-bundle
pullback identity and composition isomorphisms, after passing to isomorphism
classes. This provides an input presheaf for a later intrinsic character map;
it does not itself construct that map or prove independence of a chosen
trivialization for a character.

The provenance is internal and derived from `HomFamilyPullback`,
`LineBundlePullback`, the canonical module pullback comparisons, and the
standard categorical isomorphism-class quotient. This narrowly concerns the
trivial homomorphism pullback condition; it introduces no ordinary relative
Picard representability, descent, or duality assertion.
