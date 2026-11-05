# Uniform convolution exponents of finite commutative Hopf algebras

Authors: Workers 1575 and 16 (characteristic-zero reducedness input).

This internal algebraic development supports the unrestricted finite group scheme
uniform exponent theorem. The coordinate algebra is commutative, while its
coalgebra is allowed to be noncocommutative.

Postcomposition and forgetting multiplicativity give monoid morphisms on
convolution monoids. A convolution product of maps with values in ideals I and J
has values in IJ, as follows by writing the comultiplication as a finite sum of
pure tensors. Induction gives the corresponding assertion for powers. A map with
values in a nilpotent ideal is therefore convolution nilpotent.

A finite dimensional commutative algebra is Artinian and has finitely many
maximal ideals. There are finitely many algebra morphisms from it into each
residue field. Thus the product of the residue-field convolution monoids is
finite. The universal point is a unit, so its image in this product has finite
order. Consequently a single positive convolution power minus one has all its
values in the intersection of the maximal ideals, which is the nilradical.

If the algebra is reduced, the nilradical is zero, and this already gives a
positive convolution exponent. In positive characteristic p, the nilradical
is nilpotent because the algebra is Artinian. The ideal-valued convolution
lemma makes the difference from one nilpotent in the ring of linear maps
with convolution multiplication. The characteristic-p binomial identity
then kills that difference by some power of p. This argument only uses that
an element commutes with one, so the convolution ring may be noncommutative.
Injectivity of forgetting multiplicativity gives the same exponent for the
universal algebra-valued point.

Finally, `exists_pow_eq_one` splits the characteristic of the base field.
In characteristic zero, the imported `Langlands.FiniteHopfCharZero.isReduced`
proves the coordinate algebra reduced; the reduced-algebra branch applies.
In prime characteristic the nilpotent convolution argument applies directly.
Thus every finite-dimensional commutative Hopf algebra over any field has a
positive exponent for its universal point, without cocommutativity.

The finite residue-image and nilpotent convolution proofs are internal derived
arguments supporting the existence form of Milne, *Algebraic Groups* (2017),
Proposition 11.32, printed page 221 (PDF page 237), registered source
`milne-2017-algebraic-groups`. They do not assert the stronger bound by the
dimension of the coordinate algebra.

Convolution postcomposition reuses
`Langlands.FiniteHopfConvolutionPower.postcomp` from the existing
[FiniteHopfConvolutionPower](FiniteHopfConvolutionPower.md) module.
