# Algebra maps inducing arrows between affine bases

For commutative rings `R`, `A`, and `B`, with `R`-algebra structures on `A` and `B`,
`OpennessOfVersality.exists_affineBaseMap_eq` expresses every arrow
`affineBase R B ⟶ affineBase R A` as `affineBaseMap χ` for an `R`-algebra
homomorphism `χ : A →ₐ[R] B`. The proof lifts the scheme map through `Spec`;
the equation over `Spec R` proves compatibility with the algebra structures.

This is the unchanged theorem moved from `OpennessOfVersality/BaseLifting`
for reuse by `AffineQuotientTests`. Its full declaration name and hypotheses
are preserved.
