# Parabolic self-normalization by rational points and fpqc descent

This internal derived construction proves the exact existing all-test
`ParabolicSelfNormalizerStatement` conditional on four global statements:
`BorelConjugacyStatement`, `BorelNormalizerStatement`,
`ParabolicDynamicStatement`, and `DynamicConnectedStatement`.
The opposite open cell is supplied by its published proof.
The unconditional target remains open.

`normalizer_eq_of_dynamic_parabolic_and_borel` works over an algebraically
closed field with a smooth connected affine ambient group and a smooth connected
closed dynamic parabolic representative. An actual ambient Borel inclusion
and a factorization through this representative are additional inputs.
The existing Borel point reduction gives membership of rational normalizer
points in this subgroup, using the two stated Borel hypotheses. The actual
opposite dynamic unipotent representative has trivial intersection with the
normalizer on all tests by the published separation theorem. The proved
opposite open cell and the rational-point/Jacobson bridge then give equality
of the full subgroup functors.

`parabolicSelfNormalizerStatement_of_rational_descent` starts over an arbitrary
field with the original connected reductive group and actual parabolic inclusion.
The dynamic characterization supplies a cocharacter over that field.
After base change to its algebraic closure, range base change and dynamic
parabolic base change identify the pulled-back inclusion with the pulled-back
dynamic parabolic. Ambient smoothness and affineness follow by base change;
ambient connectedness follows from the published geometric connectedness
theorem. The dynamic connectedness hypothesis gives connectedness of the
pulled-back parabolic.

The definition of the **original** parabolic inclusion already supplies an
actual Borel over this algebraic closure and its factorization through the
pulled-back inclusion. These data allow the preceding lemma to prove the
all-test normalizer equality over the algebraic closure. The published fpqc
descent theorem then descends equality to the original field.

This route uses neither reductivity nor the parabolic predicate for the
base-changed ambient group and inclusion. It therefore removes the general
connected-reductive field-extension premise from the earlier structural
assembly. It requires rational membership only over the original algebraic
closure. All test schemes, including non-affine and nonreduced schemes, remain
in the conclusion.

`normalizerPointsEquivOfRationalDescent` transports subgroup membership through
the descended equality and uses the inverse represented-subgroup point
equivalence to return an actual morphism to the original parabolic source.
The `_comp` theorem verifies its composite with the original inclusion.
Both constructions retain arbitrary universes.
