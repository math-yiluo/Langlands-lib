# Maximal extensions of actual tori

`maximalTorusExtensionOfFiniteRingKrullDim` chooses an actual maximal torus in an
affine group over a field, containing a given closed torus, when the ambient
coordinate ring has finite Krull dimension. Its dependent-pair value contains
the commutative group scheme, its embedding in the ambient group, its maximality
proof, and a factorization witness for the original embedding.

The existence theorem
`exists_maximalTorus_extension_of_finiteRingKrullDim` justifies this choice using
the unchanged `IsTorus`, `IsClosedSubgroup` and `IsMaximalTorus` predicates. This
is a containment input to rational conjugacy, with no conjugacy assertion
assumed or proved here. All characteristics and imperfect fields are retained.
Finite Krull dimension is an explicit hypothesis; the module does not assert
that arbitrary affine groups satisfy it.

The implemented proof considers the kernels of all closed torus embeddings
through which the given embedding factors. Integrality of a torus makes each
kernel prime. Finite Krull dimension makes strict inclusion of prime ideals
well founded, so one such kernel is minimal. Any further enlargement gives a
smaller kernel; minimality forces equality. Since the ambient scheme is affine,
equality on its global affine open gives equality of ideal sheaves. Mathlib's
closed-immersion equivalence then shows that the enlargement map is an
isomorphism, as required by maximality.

This is a derived argument from the existing scheme and torus interfaces. The
finite-dimensional prime-ideal argument replaces a rank argument and does not
require choosing a common splitting field for different tori.
