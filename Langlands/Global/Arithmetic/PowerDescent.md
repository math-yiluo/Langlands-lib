# Algebraic descent and prime-power assembly for local powers

Author: Worker 384.

This module supplies elementary arithmetic helpers for the half-power target,
in namespace `Langlands.Global.Arithmetic.PowerDescent`. It implements the
exponent assembly and norm descent in Artin and Tate, *Class Field Theory*
(2009), Chapter IX, Section 1, Theorem 1, proof steps 1 and 5, printed
pp.65–66 (PDF pp.74–75). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata at PDF p.202 do not change this passage. The root
conversion and prime-power induction are internal interfaces for that proof.

`exists_unit_pow_eq_iff` identifies unit roots of a unit with field roots of
its value. For nonzero order, the root is nonzero because its power is a
unit. Order zero is handled separately by choosing the unit 1.
`exists_pow_mul_eq_of_coprime` and its unit version construct a root of the
product of coprime orders from roots of the two orders. They use Mathlib's
`pow_eq_pow_iff_of_coprime`, the exponent form of Bézout's identity.
`exists_unit_pow_eq_of_prime_power_dvd` then assembles roots of every
positive prime-power divisor of a nonzero natural number, using
`Nat.recOnPosPrimePosCoprime`. The order-one case uses the original unit.

`exists_pow_eq_degree_of_root` takes norms of a root in a finite extension:
if `b^n` is the image of `a`, then `norm(b)^n = a^[L:K]`. This uses the
multiplicativity of `Algebra.norm` and `Algebra.norm_algebraMap`.
`exists_pow_eq_of_coprime_degree` applies
`pow_mem_range_pow_of_coprime` to descend the root when `[L:K]` is coprime
to `n`. `exists_unit_pow_eq_of_coprime_degree` gives the corresponding
unit-valued result. The two fields may have independent universes, and none
of these norm statements requires a number field or a Galois extension.

`local_power_of_dvd` passes from a root in the actual finite completion to a
root of any divisor of its order by taking a power. The conditional theorem
`almostEverywherePowerHalf_of_prime_powers` applies this at every place
outside the given finite set and uses prime-power assembly. Its premise is
exactly the positive prime-power instances of the half-power implication,
with the original field universe, finite-place exception set, canonical
completion maps and units. This theorem supplies an assembly step; the
prime-power arithmetic instances remain hypotheses and are not proved here.
No almost-everywhere local-to-global power result or class-field-theory
package is used to prove the elementary descent helpers.
