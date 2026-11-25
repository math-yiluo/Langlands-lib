# Translation reduction for infinitesimal homomorphism rigidity

This internal adapter connects diagonalizable action rigidity to
homomorphism rigidity with arbitrary group-scheme target. The final lemmas retain
an explicit action-rigidity premise; this module does not prove the full statement
`MultiplicativeTypeInfinitesimalRigidityStatement`.

`translationAction f` restricts the regular multiplication action of the target
along the actual homomorphism `f`. On every test scheme it acts by multiplying
the test point by the image under `f`. If its action morphism is the second
projection, evaluation at the identity test of the source and the unit of the
target makes the underlying map of `f` equal to the unit.

`comp_eq_one_of_baseChange_eq_one` uses the multiplicative pullback
adjunction on points to transport triviality from a base change to every test
over that base. `comp_eq_one_of_quotient_eq_one` factors each algebra annihilating
the ideal through the quotient algebra, compares the resulting test scheme with
its original test over the ring, and applies that adjunction lemma.

`standard_eq_one_of_action_rigidity` applies the retained action premise to the
translation action. Its quotient-test condition follows from the quotient
lemma. `diagonalizable_eq_one_of_action_rigidity` then replaces a relatively
diagonalizable source by a standard group-algebra model, using its given
isomorphism and the diagonalizable base-change comparison, applies the
standard lemma, and cancels the source isomorphism.

The provenance is the existing Library definitions of actions, the regular
monoid-object action and scalar restriction, actual base change, the
multiplicative adjunction `baseChangePointsEquiv`, relative diagonalizability,
and its standard base-change comparison. This is a derived categorical
reduction, retaining the mathematical action-rigidity obligation. Neither target
affineness nor smoothness is assumed.
