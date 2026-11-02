# Composition of the ordinary direct-image base-change comparison

This is a derived compatibility result for the actual `pushforwardBaseChange`
constructed in `DerivedRestriction`. It applies to every two composable commuting
squares of schemes, with no Cartesian, finiteness, or quasi-coherence assumptions.
The schemes and their module sheaves have the common universe `u`.

Write the base maps as `b : S' → S` and `c : S'' → S'`, the vertical maps as
`f : X → S`, `f' : X' → S'`, and `f'' : X'' → S''`, and the upper maps as
`p : X' → X` and `q : X'' → X'`. The hypotheses are exactly
`p ≫ f = f' ≫ b` and `q ≫ f' = f'' ≫ c`. For any module sheaf `M` on `X`,
`iteratedPushforwardBaseChange` is the morphism obtained by pulling back the
comparison for the first square, applying the comparison for the second square
to `p* M`, and applying the pushforward of the canonical pullback composition
isomorphism `q* p* M ≅ (q ≫ p)* M`.

The theorem `pushforwardBaseChange_composition` identifies this morphism with
the specified comparison for the composite square, precomposed with the
canonical isomorphism `c* b* (f_* M) ≅ (c ≫ b)* (f_* M)`. Thus the equality
concerns the given canonical maps, not merely the existence of an isomorphism.

The proof uses only the existing adjunction and pushforward constructions.
`conjugateEquiv_pullbackComp_hom` derives conjugacy for the forward pullback
composition comparison from Mathlib's conjugacy for its inverse.
`homEquiv_comp_pullbackComp_hom` expresses the corresponding transport of
adjuncts, and `unit_pullbackComp_hom` expresses the unit of the composite
adjunction in terms of the two individual units. These follow from
`unit_conjugateEquiv` and the formula for the unit of a composite adjunction.
`pushforwardSquareIso_composition` proves coherence of the pushforward
comparisons by evaluating on every open: the composition comparisons act as
identities and the comparisons for equal maps act as restriction along equal
opens. Functoriality of restriction gives the desired equality.
Finally, the main theorem applies the composite adjunction's injective hom-set
equivalence. The definition of the given base-change morphism then reduces the
equality to the unit formula, naturality of the two pushforward square
comparisons, and the preceding coherence lemma.

This module proves no base-change invertibility, local freeness, or prescribed
rank assertion. Its purpose is to transport those properties across successive
squares in the direct-image criterion. No new external geometric theorem is
used; all content is derived from the named Library constructions and Mathlib
adjunction identities.
