# A reducedness criterion for commutative Artinian rings

Author: Worker 1575.

These internal commutative-algebra lemmas support the finite Hopf-algebra
characteristic-zero reducedness proof. They use Mathlib's
`IsArtinianRing.nilradical_pow_eq_iInf`, which identifies powers of the
nilradical with intersections of the corresponding powers of the maximal
ideals in a commutative Artinian ring.

If a nilpotent ideal lies in its square, the reverse containment always
holds, so it is idempotent and therefore zero. Consequently, to prove an
Artinian commutative ring reduced, it suffices to show that its nilradical
lies in the square of every maximal ideal. The characteristic-zero Hopf
argument supplies that additional containment separately.
