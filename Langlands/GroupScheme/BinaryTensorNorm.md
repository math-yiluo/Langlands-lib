# Binary reduced norm on all tensor coefficient algebras

This is an internal construction for a finite-dimensional central simple algebra `D` over a field `k`, with both types in an arbitrary universe `u`. The ring `D` may be noncommutative. The commutative test algebra `R` is arbitrary in the same universe. There is no local-field, division-ring or characteristic assumption.

## Actual norm and splitting representation

`FiniteAlgebraUnits.BinaryNorm.tensorNorm k D R` is a group homomorphism from the invertible binary matrices over `R ⊗[k] D` to `Rˣ`. It is the published canonical `CentralSimple.reducedNormUnits` of the actual algebra `Matrix (Fin 2) (Fin 2) D`, transported by the inverse of `MatrixPoints.coefficientEquiv`. Thus the definition uses the canonical reduced norm itself, rather than the determinant of the regular representation.

For a splitting chart `e : L ⊗[k] D ≃ₐ[L] Matrix I I L`, `tensorRepresentation e R` first extends the tensor coefficient by `R → L ⊗[k] R` and then applies the actual splitting map for `D`. Here `I` is any finite decidable type, and the supplied splitting chart need not be Galois. The theorem `splittingMap_binary` identifies the actual splitting map for the induced binary chart with the two-by-two block representation of the coefficient splitting map on every tensor element. Its proof uses tensor induction; the pure-tensor case checks each of the four blocks.

`tensorNorm_baseChange` states that applying the unit map for `R → L ⊗[k] R` to `tensorNorm` gives `BinaryElementary.Representation.binaryNorm` of `tensorRepresentation e R`. That latter norm is the determinant of the actual block matrix over the commutative splitting-field algebra. The proof applies reduced-norm naturality, the splitting-chart determinant formula, `splittingMap_binary` and the proved coefficient-comparison naturality.

## Norm-one identities

For every `a : R ⊗[k] D`, `tensorNorm_upper` and `tensorNorm_lower` assert that the corresponding actual binary elementary matrix has norm one. For every tensor unit `a`, `tensorNorm_diagonal_inverse` gives the same identity for `diag(a, a⁻¹)`. These use the canonical finite Galois splitting field only in the proofs: its scalar extension is faithful, and hence its unit map is injective. The block determinant identities for upper, lower and diagonal matrices prove the equalities after extension; injectivity reflects them to `R`. No extraction of roots or restriction on the characteristic occurs.

## Provenance and scope

The construction is internal, derived from the already proved matrix/tensor comparison, canonical reduced-norm naturality and splitting formulas, and binary block determinant identities. It cites no separate original-source assertion. It provides the all-test norm identities needed for subsequent lifts into the actual reduced-norm-one kernel. This module constructs no group-scheme root map, cocharacter or contraction in that kernel and makes no generation, parabolic-radical, local SK1, classification or unrestricted local Kneser–Tits assertion.
