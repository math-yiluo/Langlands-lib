# Bijectivity of the Cartier comparison on affine tests

Fix a commutative coefficient algebra `C` over `R`. An actual relative
character over `Spec C` gives a coefficient tensor by evaluation on
the universal point over `Spec (A ⊗[R] C)`. Its point and test map
come from the two tensor inclusions. For any other pair of algebra
maps out of `A` and `C`, restriction along their tensor product map
evaluates the same tensor.

The identity point gives the counit equation for this coefficient.
Over `Spec ((A ⊗[R] A) ⊗[R] C)`, multiplication of the two universal
points is induced by comultiplication on `A`. The fact that a character
is a group homomorphism gives the comultiplication equation for the
coefficient tensor. The coefficient equivalence then gives an algebra
map from the dual to `C` and hence a point of the dual spectrum.

The universal point determines the character. For any scheme with a
map to `Spec C` and a point of the Hopf spectrum, their algebra maps
into its relative global sections give a map to `Spec (A ⊗[R] C)` by
the relative spectrum adjunction. Both the point and the test map
factor through it, so naturality recovers the character value there.
Evaluating the character associated with an algebra point of the dual
on the universal point gives its original coefficient tensor. These
two facts prove `affineCharacterEquiv`.

This is the relative spectrum implementation of the group-like
coefficient argument in Demazure and Gabriel, *Groupes algébriques*,
Tome I (1970), Chapter II, §1, no. 2, 2.10(a), printed pp. 156–157.
