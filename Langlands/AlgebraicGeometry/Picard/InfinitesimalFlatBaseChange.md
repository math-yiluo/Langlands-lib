# Flat tensor base change of actual ring pullbacks

This internal prerequisite concerns commutative rings in an arbitrary common
universe. It does not assert Picard-groupoid gluing or representability.

For a commutative base ring k, a flat commutative k-algebra S, and k-algebra
maps p : R → A, q : R → B, a : A → C and b : B → C forming an actual
categorical pullback of commutative rings, `isPullback_tensor` proves that
tensoring all four rings and maps by S over k again gives an actual categorical
pullback of commutative rings. The maps are the actual tensor algebra maps
induced by the identity on S and the given maps. No surjectivity, nilpotence,
nontriviality, finiteness or field hypothesis is needed.

`tensorPullbackEquiv` constructs an actual unital ring equivalence from
S ⊗[k] R to the chosen categorical pullback of the maps S ⊗[k] A → S ⊗[k] C
and S ⊗[k] B → S ⊗[k] C. The lemmas `tensorPullbackEquiv_fst` and
`tensorPullbackEquiv_snd` identify its two projections on every element with
the tensor maps induced by p and q, respectively. Thus the equivalence
retains the given square's projection maps.

The proof forgets the given ring square to sets, reflects the same square into
k-modules, and applies Mathlib's finite-limit preservation of tensoring with a
flat module. It forgets the resulting square to sets and reflects it back into
commutative rings. The tensor maps have the same underlying functions in both
categories. Limit reflection follows from limit preservation and reflection of
isomorphisms by the respective forgetful functors. The resulting limiting
square gives the canonical isomorphism to the chosen pullback through
`IsPullback.isoPullback`; converting this isomorphism to a ring equivalence
gives `tensorPullbackEquiv`. Evaluation of its two categorical projection
identities proves the two elementwise projection formulas.

This is a derived construction from the imported Mathlib interfaces, with no
external mathematical assertion or unpublished project input. It provides the
ring base-change ingredient for affine infinitesimal-gluing arguments; scalar
extension of patched modules, local/global line-bundle patching and the actual
scheme Picard-groupoid comparison remain further obligations.
