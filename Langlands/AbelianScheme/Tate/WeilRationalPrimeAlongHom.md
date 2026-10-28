# Rational prime-adic Weil pairings along actual homomorphisms

This internal construction pulls the existing rational prime-adic Weil
pairing back in its second variable along an actual homomorphism into the
constructed dual abelian scheme. It retains the seven tensor/Picard
propositions, `HasDualScheme`, `DualSchemeGeometry`, the inverse Poincare
line bundle and evaluation, and `RelativeFiniteWeilTransitionStatement`.
The base is quasi-separated, the test scheme is arbitrary, and the prime
has `Fact p.Prime`.

`primeRationalWeilAlongHomBilinearMap` composes
`primeRationalWeilBilinearMap` with
`GroupScheme.Tate.PrimeAdic.rationalMap` of the actual `groupHom lam` in
the second variable. Its two inputs are the existing tensor products of
the integral prime-adic Tate module of A with the p-adic rationals over
the p-adic integers. Its output is the existing rational prime-adic
roots-of-unity twist. The application formula is exactly
`e(x, V_p(lam)y)`, so the inherited finite convention remains
beta(lam(y))(x).

The pure-tensor formula multiplies the two p-adic rational coefficients
and applies exactly `primeWeilAlongHomBilinearMap` to the integral
inputs. It follows from the pure-tensor formulas for the actual
prime-adic rational Tate map and the intrinsic rational Weil pairing.
Setting both coefficients to one gives compatibility with the
canonical rationalization maps. Tensor extensionality in both variables
proves that the pure-tensor formula uniquely determines this bilinear
map.

`rationalToPrime_rationalWeilAlongHomBilinearMap` compares the rational
pullback on any selected divisibility system with this prime-adic
rational pullback. It assumes that every power of p is retained.
Extraction on the actual output twist equals pairing the extracted
input Tate modules. The proof uses tensor induction in both variables,
the pure-tensor formulas for the pairings and rational extraction maps,
the existing integral pullback extraction identity, and preservation of
multiplication by the inclusion of the rationals into the p-adic
rationals. Additivity handles the induction's sum cases.

The full specialization retains every positive order. The away
specialization uses orders coprime to a natural modulus m and assumes
`Nat.Coprime p m`, so that all powers of p are retained. The two final
lemmas give the same extraction identities for the underlying values of
the full and away adelic bundles. They use the existing application
formulas identifying these bundles with the rational pullbacks. The
explicit full scalar comparison and its coupled away comparison remain
the same on both inputs and on the twist.

The provenance is internal composition and scalar extension of the
already constructed intrinsic Weil pairings and actual Tate maps,
followed by their existing prime-extraction comparisons. Any actual
polarization can be substituted for the homomorphism; its polarization
predicate is unnecessary for this construction. No arbitrary pairing
or trivialization of the roots-of-unity twist is supplied. This unit
asserts no alternation, nondegeneracy, perfectness, continuity, or
monodromy equivariance. Relative finite transition compatibility remains
an explicit theorem hypothesis.
