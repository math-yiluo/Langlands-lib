# Intrinsic split-torus valuation

For an actual split torus \(T\) over any field \(k\), and any valuation
\(v:k\to\{0\}\cup\operatorname{Multiplicative}(\mathbb Z)\), `splitValuation`
is the homomorphism \(T(k)\to X_*(T)\) determined by
\[
  \langle\chi,\omega_T(t)\rangle
    =\operatorname{ord}_v(\chi(t)).
\]
The target uses a multiplicative type tag so that this is a group homomorphism
from the multiplicative rational-point group to the additive lattice.
`IntegerValuation.orderUnits` is the positive order, the negative logarithm of
the multiplicative valuation.

The construction forms the integral linear functional of actual character
orders and applies the inverse of the perfect character–cocharacter pairing.
It uses the Library theorem
`CocharacterUniformizer.latticePairing_isPerfPair` for every actual split torus.
`splitValuation_pairing` proves the displayed formula, and
`splitValuation_unique` proves uniqueness among homomorphisms with that formula.
These are elementary construction laws, not a proof of the torus Kottwitz
existence theorem.

This is an internal implementation of the split valuation used by
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §11.1,
printed pp. 420–421, especially Proposition 11.1.1 (PDF pp. 451–452).
It deliberately works over an arbitrary valued field: finite splitting
extensions of the maximal unramified field need not be local fields.
When used in the Kottwitz norm characterization, the valuation on the
splitting field is normalized to have full integer value group.
