# Overlap components for ring tensor decompositions

This internal construction extends the published field-only
`TensorComponents` argument to arbitrary commutative rings `R` and `S` with
an `R`-algebra structure on `S`. It reuses the published finite
`sigmaSpec` isomorphism; the proof requires no field operations.

An actual `S`-algebra equivalence `S ⊗[R] S ≃ (I → S)`, with a small finite
index type, gives coordinate maps from `Spec S` to
`Spec S ×[Spec R] Spec S`. Their finite coproduct is an isomorphism:
it factors through the finite product spectrum, the spectrum of the supplied
algebra equivalence, and the affine tensor-product pullback isomorphism.

The first projection of each component is the identity. If the equivalence
sends `a ⊗ b` to `i ↦ a * s i b` for actual `R`-algebra automorphisms `s i`,
the second projection is precisely `Spec (s i)`. Both composite projections
are then isomorphisms. These identities are proved on the corresponding
ring homomorphisms by the pure tensor formulas.
