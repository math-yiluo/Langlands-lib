# Away localization as actual outside-prime integers

This derived construction is arithmetic infrastructure for the function-field
integral model in Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), Example 4.2, printed pages 9–10. The source requires a finite locally free
extension of the actual S-integer rings. Comparing suitable S-integer rings with
localizations of finite normalized affine charts will permit finite normalization
without assuming separability of the original field extension. The generic
comparison in this file is not asserted as a separate theorem in Conrad.

For a Dedekind domain A, its original fraction field K, and a nonzero element t
of A, `dedekindAwaySubalgebra` is the localization at powers of t realized as an
actual A-subalgebra of K. `mem_dedekindAwaySubalgebra_iff` proves that membership
means valuation at most one at every original height-one prime not containing
t. Consequently `dedekindAwaySIntegerEquiv` identifies this localization with
Mathlib's actual integer subalgebra outside the set of primes containing t.
It is an A-algebra equivalence and fixes the underlying elements of K. The domain
ring and the set of exceptional primes are constructed from A, K and t; no
outside-prime membership equivalence is assumed.

For the forward direction, the denominator of a localization element is a power
of t. At a prime not containing t its valuation is one, whereas the numerator
has valuation at most one. For the converse let D be the actual localization
subalgebra. It is again Dedekind with fraction field K. Every height-one prime Q
of D contracts to a nonzero prime P of A: localization maps that contraction
back to Q. The image of t is a unit in D, so P does not contain t. The
localization of A at P lies in Q's valuation ring, since its permitted
denominators have valuation one at Q. The nontrivial discrete valuation overring
comparison makes these valuation rings equal. The hypothesis therefore places
the given field element in every height-one localization of D. Their intersection
is D, which proves membership and the stated equivalence.

The domain and fraction field have independent arbitrary universes. There is no
finite-constant, field-extension or separability assumption in this generic
comparison. Choosing suitable actual function-field exceptional sets, proving
their cofinality, and instantiating finite locally free S-integer extensions and
the adelic Weil comparison remain obligations of the host task.
