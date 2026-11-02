# Prime-power cyclotomic Galois groups

Authors: Worker 384 and Worker 1244.

This is an internal arithmetic component of the proof of Artin–Tate,
*Class Field Theory* (2009), IX.1, Theorem 1, printed pp.65–66
(PDF pp.74–75). The appended errata (PDF p.202) contains no relevant
correction. Worker 1244 supplied the component interface and proof plan;
Worker 384 implemented the Lean proofs. The principal-unit subgroup and
its supporting lemmas are derived infrastructure, rather than new
hypotheses about almost-everywhere powers.

The namespace is `Langlands.Global.Arithmetic.CyclotomicPrimePowerGalois`.
Only Mathlib modules are imported. The two field universes are independent;
the cyclotomic lemmas require no number-field or characteristic-zero
assumption.

`principalUnits p n k` is the kernel of the reduction homomorphism
from units modulo `p^(n+k)` to units modulo `p^k`. This definition is
available for all natural `p`, `n`, and `k`; the subsequent cardinality
and cyclicity conclusions carry their own hypotheses.

`finrank_dvd_totient` proves that a cyclotomic extension of order `m`,
where `m` is nonzero, has degree dividing `m.totient`. The cyclotomic
character injects its automorphism group into the units modulo `m`.
Cyclotomic extensions are finite Galois, so the automorphism cardinality
is the field degree; Lagrange's theorem gives the claimed divisibility.

`card_principalUnits` proves that this kernel has cardinality `p^n`
when `p` is prime and `k` is nonzero. Reduction on units is surjective.
The kernel-index identity expresses its order as the quotient of the
two unit-group orders, and the prime-power totient formula gives `p^n`.

`isCyclic_principalUnits` additionally assumes `k + 2 ≤ p*k`.
Mathlib's `ZMod.orderOf_one_add_mul_prime_pow` gives the residue `1+p^k`
order `p^n` modulo `p^(n+k)`. Its positive order supplies a unit, and
reduction of that unit is one. Thus the kernel has an element of order
its full cardinality and is cyclic. This stable-range hypothesis covers
the needed odd-prime case with `k ≥ 1` and the prime-two case with
`k ≥ 2`.

`autToPow_mem_principalUnits` assumes a cyclotomic extension `E/B` of
order `p^(n+k)` and a primitive `p^k`-th root `ξ` in `B`. It proves that
each value of the cyclotomic character lies in `principalUnits p n k`.
Indeed, if `ζ` is the distinguished primitive root in `E`, then
`ζ^(p^n)` is primitive of order `p^k`. It is a power of the image of
`ξ`, so every `B`-automorphism fixes it. The character formula then
makes the character exponent congruent to one modulo `p^k`.

Finally, `isCyclic_and_finrank_eq_pow` assumes `p` prime, `k ≠ 0`,
`k + 2 ≤ p*k`, and the same root `ξ`. It proves
`IsCyclic (E ≃ₐ[B] E) ∧ ∃ e, Module.finrank B E = p^e`.
The preceding membership result restricts the injective cyclotomic
character to the cyclic principal-unit subgroup. Hence the automorphism
group is cyclic and its order divides `p^n`. A divisor of a prime power
is a prime power, and the finite Galois degree formula finishes the proof.
The auxiliary exponent `e` is existential; the theorem does not assert
that the extension has degree exactly `p^n`.

This component proves no local-to-global power assertion by itself. The
remaining argument must use the local power premises and perform the
arithmetic descent to the original number field.
