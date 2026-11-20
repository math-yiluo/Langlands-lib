# The cyclotomic character on actual geometric Frobenius lifts

`absoluteCyclotomicCharacter` is an internal construction for comparing
pure weakly associated families. It composes Mathlib's cyclotomic
character on ring automorphisms with the action of the actual absolute
Galois group on its algebraic closure. Mathlib's continuity theorem for
this composite gives continuity in the Krull topology.

Over a characteristic-zero field, the character's reductions are
determined by the action on one primitive root at each level. Transport
of roots along the chosen algebraic-closure embedding gives compatibility
with Galois restriction.

Away from the cyclotomic prime, a root of unity of prime-power order belongs
to the spectral valuation ring. The order is a unit there, and two such
roots with the same residue agree, by the simple-root uniqueness lemma in
`Langlands.Galois.Local.SeparableUnramifiedArithmeticProof`. Inertia fixes
the residues. The inverse of a geometric Frobenius lift raises them to the
residue cardinality power. Uniqueness lifts these two actions to the roots
of unity, so the character is one on inertia and takes the residue
cardinality as its value on the inverse of every geometric lift.
