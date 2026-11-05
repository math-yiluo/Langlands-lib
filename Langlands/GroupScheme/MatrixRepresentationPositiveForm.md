# Positive-form normalization of actual matrix representations

This is an internal change-of-basis construction. It combines the published
spectral positive square root in `AlgebraicPolar`, the actual scheme
conjugation in `MatrixRepresentationConjugate`, and the canonical evaluation
topology in `InfinitePlaceMatrixRealization`. It asserts no new
literature identification or reductive-group existence theorem.

## Matrix construction

The scalar field `k : Type u` is arbitrary with `RCLike k`. The index type
`n : Type` is finite with decidable equality and may be empty. For an
invertible matrix `J : GL n k` whose underlying matrix is positive definite,
`normalizingMatrix J hJ` is the spectral power `J^(1/2)` already constructed
in `AlgebraicPolar`. Write this matrix as `C`. The theorems
`normalizingMatrix_posDef`, `star_normalizingMatrix`, and
`normalizingMatrix_mul_self` give positive definiteness, `C* = C`, and
`C C = J`, respectively. Here star is conjugate transpose.

The identity `star_conj_normalizingMatrix` states

\[
 (C g C^{-1})^* = C(J^{-1}g^*J)C^{-1}.
\]

The proof expands star of a product, uses Hermitian symmetry of `C`, substitutes
`J = C C`, and cancels invertible factors. In particular it fixes the direction
of the basis change: the new coefficient matrix is `C g C⁻¹`.

For a group `A : Type v` in an independent universe, `normalizedHom ρ J hJ`
conjugates a supplied coefficient homomorphism `ρ : A →* GL n k` by `C`.
If its actual range is stable under `g ↦ J⁻¹ g* J`,
`star_mem_normalizedHom_range` proves that the normalized range is stable
under ordinary conjugate transpose. The proof extracts an original range
preimage of the form adjoint, takes that same group element in the normalized
representation, and applies the displayed identity. It does not assume that
the form adjoint fixes each element.

## Actual scheme representation

Let `G` be an actual group scheme over `Spec k` and `ρ` an actual matrix
representation of it. `matrixBasePoint C` turns a matrix over `k` into an
actual base point of the general linear group scheme. It uses the existing
affine coefficient equivalence over the self algebra `k`, preceded by the
canonical morphism from the identity base scheme to that self-algebra
spectrum. Pulling this base point back to the self-algebra spectrum recovers
the original coefficient point. This is the private
`constantPoint_matrixBasePoint` calculation.

`conjugate_matrixBasePoint_affineMatrix` identifies conjugation by this
single actual base point with `C ρ(x) C⁻¹` on every actual affine `k`-point.
The construction is an actual scheme morphism and hence has compatible
actions on all test schemes; the explicit coefficient formula asserted here
is over the base field itself.

`isClosedSubgroup_conjugate` proves that a supplied closed representation
remains closed after any such actual base-point conjugation. Its underlying
scheme map is a composite of the original closed immersion with a scheme
isomorphism.

`positiveFormConjugate ρ J hJ` uses the positive square root for this actual
scheme conjugation. Its base-field coefficient homomorphism equals
`normalizedHom` literally, by `positiveFormConjugate_affineMatrix`.
Consequently `star_mem_positiveFormConjugate_range` transfers the explicit
form-adjoint stability premise to ordinary adjoint stability of the actual
coefficient image. `isClosedSubgroup_positiveFormConjugate` preserves the
scheme-theoretic closed-embedding property.

Finally, `exists_closed_starStable_of_positiveForm` packages the resulting
actual representation, its closed immersion, its closed embedding on actual
affine `k`-points with the existing regular-function evaluation topology, and
ordinary adjoint stability. The topology is unchanged: the closed-embedding
conclusion uses the published `isClosedEmbedding_affineMatrix` theorem for
this newly constructed scheme representation.

The positive form and stability of the original image under its adjoint are
explicit premises. This auxiliary construction does not establish their
existence from geometric reductivity, compare arbitrary actual parabolics to
cocharacter parabolics, or prove the host
`InfinitePlaceGroupPoints.ParabolicIwasawaStatement`. Those remain separate
obligations of the full local existence proof.
