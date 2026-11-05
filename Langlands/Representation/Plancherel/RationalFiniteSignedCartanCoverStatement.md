# Finite signed Cartan charts on actual rational points

`Langlands.Plancherel.RationalFiniteSignedCartanCoverStatement.{u}` is an
internal consequence of supplied actual Cartan data. It concerns a connected
reductive group over an arbitrary nonarchimedean local field, a maximal split
torus, a generic cocharacter with finitely many simple roots, the published
standard-cocharacter statement, and a supplied apartment, point, and torus
centralizer data with the published standard-Levi compatibility. The finite
lattice transversal is also supplied.

The conclusion covers every actual rational point by finitely many
cocharacter charts between two elements of the very same supplied special
compact subgroup. A finite set `T` of rational points gives the remaining
translates. The charts are indexed by `Fin k → Bool`, and each chart has
generators indexed by `SimpleRoot i ν ⊕ Fin k`. These generators are
integrally linearly independent and pair nonnegatively with every simple
root. Each point is a product
`k₁ * uniformizerPowers i (sum a, n a • gen ε a) * t * k₂`,
where all coordinates `n a` are natural numbers. There is no additional
central factor.

The internal derivation first uses the actual Levi-Cartan witness and its
uniformizer valuation to express each middle element using a cocharacter
whose simple-root pairings have a common lower bound, followed by one point
from a finite set. The finite signed chamber lattice theorem retains a basis
of the full common pairing kernel among its generators. Its finite
cocharacter translates combine with the finite rational-point translates.
Commutativity of uniformizer powers puts these products in the stated order.
The split torus has a finite torsion-free integral cocharacter lattice.

This strengthens the finite-chamber cover modulo the full rational center
for this purpose by retaining its kernel directions in finitely many
independent charts. Empty simple-root types and zero kernel rank are allowed.
It asserts no existence of the supplied apartment, Levi compatibility,
standard cocharacters, or simultaneous compact-open basis. Compactness of
the supplied subgroup, coefficient bounds, positive characters on the
charts, and comparison with matrix norms remain separate obligations.
