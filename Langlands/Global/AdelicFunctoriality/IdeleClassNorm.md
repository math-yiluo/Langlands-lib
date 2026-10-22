# The continuous norm on actual idele classes

For number fields `K : Type u` and `L : Type v` with `Algebra K L`,
`ideleClassNorm` is the continuous multiplicative homomorphism from the
actual idele-class group of `L` to that of `K`. The universes are independent.
It sends the class of an idele `a` to the class of `ideleNorm a`, where
`ideleNorm` is the previously constructed product of the genuine local
determinant norms over the places above each base place. The construction
has no extra arithmetic hypothesis.

The imported theorem `completedTensorComparison` proves bijectivity of the
canonical tensor maps at every finite and infinite place. The first
projection of the imported theorem `normAssembly` converts this result to
the principal-adele identity. The resulting specialization
`adeleNorm_principal` states equality with the diagonal image of
`Algebra.norm K x`, for every `x : L`, including zero.

`ideleNorm_principal` applies the published unit-level reduction to this
identity. The field-unit norm is exactly `Units.map (Algebra.norm K)`.
`ideleNorm_principal_le` then proves that the raw norm preserves the
principal subgroup, using that field-unit norm as its witness.

`ideleClassNorm` instantiates `ideleClassNormOfPrincipalFormula` with the
proved principal identity. This uses the existing `QuotientGroup.map`
construction and its continuity proof. The topology on ideles tracks both
the value and inverse of a unit, and the topology on idele classes is the
actual quotient topology. Thus continuity is contained in the constructed
continuous homomorphism; `continuous_ideleClassNorm` exposes it directly.

`ideleClassNorm_mk` is the defining equation on representatives.
`ideleClassNorm_principal` rewrites that equation with the field-unit
identity and exhibits a principal representative in the target, whose
class is one. Finally, `ideleClassNorm_unique` applies the published
uniqueness result: every continuous homomorphism with the same equation
on representatives equals this one.

This is a derived construction from the published tensor comparison,
determinant reduction and quotient descent. Those imports supply all
arithmetic premises; the module does not introduce a proposed norm as data
or assume its principal compatibility. Its laws expose the construction
for downstream use. Extension-of-scalars inclusions have the opposite
direction and are separate maps.

The original arithmetic context is Andre Weil, *Basic Number Theory*,
second edition (1973), Chapter III section 4, Theorem 4 and Corollary 3,
printed pp. 56-58 (PDF pp. 73-75), for completed tensor decomposition and
the local/global norm identity; Chapter IV section 1, Corollary 3, printed
p. 64 (PDF p. 81), for the adelic product; and Chapter IV sections 3-4,
printed pp. 71-76 (PDF pp. 88-93), for the idele topology and principal
quotient. Registered original: `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The proof route here is the specialization of the existing Lean
constructions described above.
