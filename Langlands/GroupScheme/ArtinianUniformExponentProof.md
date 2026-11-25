# Proof of the Artinian-local uniform exponent theorem

This module supplies the internal residue-exponent construction and proves the `ArtinianUniformExponent.Statement` in every
universe. The target concerns all points on all test schemes, with no flatness
or commutativity hypothesis.

A quasi-compact locally quasi-finite group over an Artinian local base is finite.
The published finite-field theorem gives a positive exponent on the residue
fibre. The internal definition `residueExponent` chooses this integer once;
its positivity and reduction property are proved before the two branches. The multiplicative comparison of actual affine points under base change
then makes the same power trivial modulo the extended maximal ideal in every
coefficient algebra.

In positive residue characteristic `p`, the maximal ideal is nilpotent and
contains `p`. The nilpotent coefficient-kernel helper kills the
remaining point by a fixed power of `p`. In characteristic zero the finite
coordinate Hopf algebra is formally unramified by the characteristic-zero
helper. Uniqueness of algebra lifts across nilpotent ideals makes the residue
exponent lift unchanged. The chosen affine universal point finally yields the
same exponent on every test scheme by precomposition.

The route implements the Artinian step of SGA 3, Exposé IX, Lemma 6.1 (registered
source `sga3-expose-ix-gille-polo-2009`, printed pp.52–53), using Kähler
differentials and Nakayama in the characteristic-zero branch. The full global
uniform exponent theorem requires separate reduction and exhaustion
arguments; it is `quasiFiniteCommutativeUniformExponent` in
`Langlands.GroupScheme.QuasiFiniteCommutativeUniformExponentProof`, which
imports this module.
