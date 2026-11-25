# Transpose charts and the opposite algebra in norm-one descent

This internal construction makes the algebra sign convention explicit before
the Brauer-class comparison.

The scalar-extension/opposite equivalence retains the commutative
splitting-field factor. Composing it with the opposite of the original
chart and the transpose equivalence gives `oppositeChart` on the actual
opposite algebra. Its pure-tensor formula is exactly the transpose of
the original chart.

The inverse transpose of each constructed Galois conjugator intertwines
the transposed constant matrices. For any Galois splitting extension,
transpose identifies the opposite of the original actual fixed algebra
with the actual fixed algebra of the opposite chart. The latter is
identified with the original opposite algebra by the infinite-Galois
algebra-recovery construction.

The intended convention is therefore the original algebra for the
standard column matrices and its actual opposite for the transposed
dual algebra. This module does not introduce Brauer quotient operations
or assert the general Tits-obstruction comparison. It gives the actual
algebra equivalences and the inverse-transpose conjugator equation
needed for that comparison.

Provenance is internal: scalar extension commuting with opposites,
the actual matrix transpose algebra equivalence, and the constructed
Galois algebra-recovery equivalences supply every map. The conjugator
equation is proved by transposing the original equation and
multiplying by its inverse transpose. All fields and algebras may have
the same arbitrary universe `u`. The fixed-algebra equivalences assume
only that the splitting field extension is Galois, and may use an
infinite extension. No characteristic or perfection condition occurs.
