# Lattice-chain scalars from a normalizing field

The field is finite over the base because evaluation on a nonzero vector
embeds it linearly into the ambient vector space. Integral elements preserve
each lattice by the monic relation argument in `LatticeChainShifts`. The action
of the integral closure therefore gives the same sets of vectors a lattice
structure over the extension integers. Finite generation follows from the
original finite generating set, and spanning over the base implies spanning
over the extension.

A unit of the extension integer ring has shift zero, by applying the
integrality inequality to the unit and its inverse. The base uniformizer
shifts by the period. Its factorization into a unit times a power of an
extension uniformizer shows that the latter's shift times the ramification
index is the base period. This shift is positive and gives the period of the
chain over the extension integers, with its original lattice indices.

The construction supplies the extension lattice chain used in the proof of
Bushnell–Kutzko (1993), (1.4.15), printed p. 41. It implements the period
and lattice comparison from §1.2, printed pp. 24–25.
