# Rational and adelic Weil pairings along actual homomorphisms

This internal construction pulls the existing rational Weil pairing back
in the second variable along an actual homomorphism from the abelian
scheme to its constructed dual. It retains the seven tensor/Picard
propositions, `HasDualScheme`, `DualSchemeGeometry`, the inverse Poincare
line bundle and evaluation, and `RelativeFiniteWeilTransitionStatement`.
The base is quasi-separated, and the test scheme is arbitrary.

`rationalWeilAlongHomBilinearMap` composes the second variable of
`rationalWeilBilinearMap` with `GroupScheme.Tate.rationalMap` of the actual
`groupHom lam`. Both inputs are the existing `Q tensor_Z Integral`
carriers for the same selected divisibility system. The value remains
in the existing rational roots-of-unity inverse limit twist. Its
application formula is `e(x, V(lam)y)`, preserving the finite convention
beta(lam(y))(x).

The pure-tensor formula multiplies the two rational coefficients and
uses exactly `integralWeilAlongHomBilinearMap`. Its proof uses the
published pure-tensor formulas for the rational Tate map and rational
pairing. Setting both coefficients to one gives compatibility with the
canonical rationalization maps. The full-to-away restriction formula
follows by tensor induction in both variables and the integral
coordinatewise restriction identity. The full rational pairing is the
specialization to the predicate that retains every positive order; the
away pairing retains orders coprime to the natural modulus.

`adelicWeilAlongHomBilinearMap` composes the existing adelic Weil pairing
with `Tate.finiteAdeleHomMap` of the rationalization of the actual
homomorphism. It uses the same explicit
`RationalProfiniteIntegerAdeleComparison` on both inputs and the twist.
It is bilinear over the existing `Global.FiniteAdeles Q`. Its application
lemma identifies its value with the rational pullback above, using the
published recovery of the actual map from its rationalization.

`awayAdelicWeilAlongHomBilinearMap` makes the same construction with the
existing away adelic pairing and `Tate.primeToFiniteAdeleHomMap`. The same
coupled `PrimeToRationalProfiniteIntegerAdeleComparison h m` supplies the
scalar structures on both inputs and the twist. Its application lemma
identifies its value with the selected rational pairing on orders
coprime to the modulus. Consequently the restriction formula also
compares the values of these full and away adelic bundles.

The provenance is internal composition of the already constructed
intrinsic pairings with the existing functorial rational Tate maps.
A polarization can be substituted for the homomorphism; its polarization
predicate is unnecessary for these definitions. No arbitrary bilinear
form, new adelic ring, roots-of-unity basis, or twist trivialization is
introduced. This unit asserts no alternation, nondegeneracy, perfectness,
continuity, prime-adic extraction, or monodromy equivariance.
