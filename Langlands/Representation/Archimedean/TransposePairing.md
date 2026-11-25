# Inverse-transpose pairings for archimedean local modules

This internal interface isolates the local archimedean pairing obligation needed
by the proof of `CuspidalTransposeInverseContragredientStatement`. It works for `RCLike` scalars, in particular for the real and complex
groups, and retains an arbitrary universe for the representation carrier.
It states no existence theorem.

`compactIota` is the actual map `k ↦ transpose(k⁻¹)` on the standard maximal
compact group `Matrix.unitaryGroup (Fin n) 𝕂`. The implemented proofs show that it
is a multiplicative involution. `compactIota_eq_map_star` identifies it with
entrywise conjugation; `compactIota_real` specializes it to the identity on the
real orthogonal group.

`matrixLieIota` is negative ordinary transpose on the matrix Lie algebra,
viewed over the real numbers. The bracket proof reverses the two factors under
transpose and uses the minus sign. `complexifiedMatrixLieIota` is its
complexification: it sends `z ⊗ X` to `z ⊗ (-transpose X)`. In particular, for a
complex matrix Lie algebra the scalar extension is from the underlying real
Lie algebra, as in `IsComplexGKModule`; it is not an identification with just
one complex matrix Lie algebra. Both Lie maps are proved involutive.

`IsTransposeInvariantGKPairing 𝕂 n ρ π B` means that the complex bilinear form
`B` is invariant for the compact action on its first variable and the
inverse-transpose compact action on its second, and that the sum of its two
Lie derivatives is zero, with the second derivative twisted by
`complexifiedMatrixLieIota`. The Lie condition quantifies over every element
of the genuine complexification.

`HasNonzeroTransposeGKPairing 𝕂 n ρ π` asserts the existence of such a form with
`B ≠ 0`. It does not impose smoothness or admissibility by definition, prove
existence, or assert a bijection onto all compact-finite dual functionals.
Those are separate mathematical obligations.

The provenance is internal. These definitions write the same inverse-transpose
and negative-transpose conditions as the global
`OperatorRealization.IsTransposeInvariantPairing` at a single real or complex
place, using the existing local compact and Lie carriers from `GKModule`.
The elementary matrix and scalar-extension proofs implement the coordinate
formulas directly. No local Gelfand--Kazhdan theorem or global factorization is
assumed or claimed.
