# Proof of irreducible degree divisibility

`Langlands.irreducibleDegreeDivisibility` proves
`IrreducibleDegreeDivisibilityStatement`, using the character-integrality
argument of Serre, *Linear Representations of Finite Groups*, §6.5.

For a conjugacy class `c`, sum the action operators `ρ(g)` over its
members. Conjugation permutes that finite set, so the operator commutes
with every `ρ(h)`. Schur's lemma expresses it as a scalar times the
identity. The sum is the image of a class sum in `ℤ[G]` under the
representation algebra map. It is integral over `ℤ` because `ℤ[G]` is a
finite `ℤ`-module. The scalar is therefore integral as well, by the
injective scalar algebra map into the endomorphism ring. Taking traces
identifies this scalar with `(∑_{g ∈ c} χ(g)) / dim V`.

Character orthogonality gives `∑_g χ(g) χ(g⁻¹) = |G|`. Partition this sum
by conjugacy class and divide by `dim V`. Each summand is the scalar just
computed times `χ(g⁻¹)` for a representative of the class. The latter is
integral by the finite-group character lemma, so their sum is integral.
This sum is the rational `|G| / dim V`. Integrality descends through
`ℚ → ℂ`; since `ℤ` is integrally closed in `ℚ`, the rational quotient is
an integer. Clearing its nonzero denominator gives the natural-number
divisibility.

`irreducibleDegree_primePow_of_isPGroup` applies this divisibility to the
order of a finite `p`-group and uses the characterization of divisors of
a prime power. It does not assert anything about restrictions of
representations to wild inertia.
