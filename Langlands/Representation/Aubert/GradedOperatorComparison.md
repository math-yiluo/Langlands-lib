# Passing from homogeneous operators and segment monomials to the whole ring

This is an internal algebraic extension module on the actual graded
Grothendieck carrier. Its parameter `D` is a family of integer-linear
endomorphisms of the actual rankwise exact K0 groups. The subsequent Aubert
comparison specializes `D` to the actual support-adjusted operator.
The present module does not claim representation-theoretic conditions for
an arbitrary family.

`HomogeneousOperatorMultiplicativityStatement` expresses the precise
rankwise induction-product identity for `D`. The theorem
`gradedOperator_multiplicative_of_homogeneous` extends it to
`GradedOperatorMultiplicativityStatement` on all finite-support graded
classes. The proof compares two bilinear maps on pairs of homogeneous
inclusions, applies the already proved multiplication and operator
formulas, and then uses both direct-sum universal properties.

`GradedOperatorUnitStatement` specifies preservation of the actual trivial
line class in rank zero. `GradedOperatorSegmentExchangeStatement`
specifies the unsigned exchange between actual segment-socle and
special-quotient graded classes. These are explicit conditions, not
automatic consequences of an arbitrary additive extension.

With the constructed induction ring and proofs of multiplicativity and
unit preservation, `gradedOperatorRingHom` constructs the corresponding
whole-ring endomorphism with underlying map `gradedOperator D`.

`gradedLinearMap_ext_monomials` is the additive extension result: if the
actual segment monomials span, two integer-linear maps agreeing on all
those monomials agree on all classes. It does not treat agreement on
individual segment generators as an additive basis argument.

`gradedOperatorRingHom_eq_zelevinsky` provides the alternative polynomial
universal-property passage. Given the exact polynomial comparison and the
operator's product, unit and segment formulas, it compares the two
endomorphisms after the actual polynomial equivalence. Integer coefficient
maps agree by uniqueness, and the segment variables agree by the supplied
exchange formula. Surjectivity of the actual polynomial comparison then
gives equality of ring endomorphisms on the whole actual graded K0.

This construction implements the algebraic passage used in Aubert 1995,
Theorem 2.3, printed p.2185, with the monomial correction recorded in
`notes/henniart/aubert-duality-route.md`, and Zelevinsky 1980,
Corollary 7.5 and §9.12. Its proof route is the polynomial universal
property rather than a new representation-theoretic calculation.
It retains the complex `PadicField` scope, independent field/carrier
universes and all actual-model dependencies of the preceding modules.
The representation-theoretic product and exchange formulas and polynomial
comparison are displayed premises; this extension does not discharge them
or absorb them into an external Chapter V structural boundary.
