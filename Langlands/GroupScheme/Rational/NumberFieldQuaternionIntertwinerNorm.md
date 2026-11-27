# Local-to-global principle for reduced norms of intertwiners

Module: `Langlands.GroupScheme.Rational.NumberFieldQuaternionIntertwinerNorm` (namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`).

- `intertwinerDefect μ h g` is the `F`-linear map `x ↦ μ x h - g x` on an `F`-algebra `D`;
  `lTensor_intertwinerDefect` computes its scalar extension to `R ⊗ D` as the same
  expression with `1 ⊗ h`, `1 ⊗ g`.
- `conjugateProductQuadratic τ ℓ` is the quadratic form `x ↦ ℓ (x τ x)`;
  `conjugateProductQuadratic_comp_baseChange` describes the scalar extension of its
  restriction to a subspace.
- `HasIntertwinerOfNorm μ h g R` is the proposition that some `x ∈ R ⊗ D` satisfies
  `μ x h = g x` and has reduced norm `μ`.
- `exists_intertwiner_of_local`: over a number field `F`, for a central quaternion division
  algebra `D` (with `σ`, `hdim`, `hsym` supplying the canonical conjugation `τ`),
  `μ ∈ F`, `h g ∈ D`: if `HasIntertwinerOfNorm μ h g` holds at the completion of every
  infinite and every finite place, then some `y ∈ D` satisfies `μ y h = g y` and
  `Nrd y = μ`.

Proof: the intertwiners form the subspace `V = ker (intertwinerDefect μ h g)`. On `D` the
form `x ↦ ℓ (x τ x)` is the reduced norm (`quaternionConjugation_norm`, `ℓ` a left inverse of
the structure map), which is anisotropic since `D` is a division algebra, so its restriction
`Q` to `V` is nondegenerate. Over a completion `K`, a local intertwiner lies in the kernel of
the extended map, which is the image of `K ⊗ V` (flatness of `K` over `F`,
`Module.Flat.ker_lTensor_eq`), so `Q` represents `μ` over `K`. The local-to-global principle
for representations by quadratic forms, `Langlands.numberFieldQuadraticRepresentation`, gives
`y ∈ V` with `Q y = μ`. For a quadratic extension `F(h)`, this is the Hasse norm theorem in the
form used for the rank-one special unitary group (Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §3.3, Theorem 6(a), printed p. 41, and §5.11).
