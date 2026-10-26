# Flattened normalized opposite Jacquet comparison

`Parabolic.flattenedOppositeJacquetComparison` proves the exact closed
`FlattenedOppositeJacquetComparisonStatement.{uK,uF,uV}`. Its two clauses are
literal equality of the opposite radicals over every commutative ring and
the representative-preserving equivalence of the actual normalized opposite
Jacquet representations over the p-adic field. The ring, field and
representation-carrier universes are independent.

The first clause imports `flattenedOppositeUnipotentComparison`, already proved
from the actual ordered block coordinates. This subgroup equality identifies
the composed and standard flattened coinvariant quotient modules. Transport
along that equality is a linear equivalence and sends the class of each
original vector to the same class.

The companion `FlattenedRefinementModulusCalculation` module proves the actual
full modulus equality by determinant products and the lexicographic partition
of fine-block pairs. Thus the final theorem discharges the modulus premise of
its local helper. It assumes neither a supplied character equality nor an
equivalence of the normalized representations.

The canonical positive square root and complex embedding carry this equality
of actual full positive characters to equality of their positive halves.
The standard opposite action on a class uses this positive upper half,
since its defining opposite full modulus is the inverse of the upper full
modulus. The proof expands that action directly.

Every quotient vector has an original representative. On those representatives,
the two normalized actions agree by the half-character equality and
`flattenedLeviEquiv_embedding`, which identifies their actual ambient matrices.
This proves equivariance of the quotient linear equivalence and retains the
representative formula `[v] ↦ [v]`.

These are internal consequences of the existing matrix, character and quotient
definitions. No external mathematical assertion is attributed to this proof.
There is no rank, smoothness, admissibility, irreducibility or finite-length
restriction. Empty block shapes and zero representations are included.
The result compares the composed opposite quotient with the standard flattened
opposite quotient; it does not prove the all-regular multiplicity comparison,
continuation or an irreducible-head assertion.
