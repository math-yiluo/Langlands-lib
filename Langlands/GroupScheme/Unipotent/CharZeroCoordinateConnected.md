# Connectedness of characteristic-zero unipotent coordinate algebras

This internal derived module proves a coordinate-algebra case of
characteristic-zero unipotent connectedness. It uses the published
`corepresentedMatrixUnipotence` criterion and
`isLocallyConilpotent_of_isMatrixUnipotent` to put every coordinate into a finite
stage of the reduced-translation filtration.

For a rational character `v`, coordinate right translation minus the identity
is `rightAct (v - counit)`. This follows from linearity of `rightAct` in its
functional and the counit identity. Since `(v - counit) 1 = 0`, each application
lowers the reduced filtration. Thus every coordinate is killed by some power of
translation minus the identity.

For a Noetherian coordinate algebra, the finite-idempotent result and the
periodic-vector lemma then make every rational right translation fix every
idempotent. Translation has an algebraic right inverse, namely translation by
the inverse point. Evaluating the fixed-coordinate identity at the identity
point shows that every rational point takes the same value on the idempotent.

When the field is algebraically closed and the coordinate algebra is reduced
and of finite type, the published reduced rational-point density theorem
`KostantRosenlicht.eq_zero_of_forall_algHom` makes each idempotent equal to its
counit value as a constant function. An idempotent in the field is zero or one.
The correspondence between idempotents and clopen subsets of the prime spectrum
then proves that the spectrum is connected. The group coordinate counit also
ensures that the algebra is nontrivial and its spectrum is nonempty.

The proof is a derived argument from existing Library and Mathlib results; it
does not use characteristic-zero connectedness or a split-unipotence theorem as
an input. The reducedness hypothesis is explicit in this coordinate lemma.
The entry declaration `connectedSpace_primeSpectrum_of_isUnipotent` is a
proof-producing `def`, following the Library's convention for intermediate
derived implications. The general group-scheme connectedness statement still
requires reduced coordinates from Cartier's theorem and descent from an
algebraic closure.
