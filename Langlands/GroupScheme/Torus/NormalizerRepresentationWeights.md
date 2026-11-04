# Normalizer action on faithful representation weights

This is an internal supporting construction for the full Weyl-image finiteness
argument. It works over every field `k : Type u`, for a finite index type `I`
(including the empty type), any actual group scheme `G` over `Spec k`, any matrix
representation `ρ` on `Fin N`, and any homomorphism `j` from the standard split
torus to `G`. The results in this module require neither a faithful
representation nor a closed embedding: those assumptions are needed later to
show that the nonzero weights generate the whole character lattice.

Write `E = splitTorus.characterLatticeEquiv k I`. The actual additive
automorphism `RepresentationWeightWeylFinite.exponentAut I σ`, reused here
as `exponentAut I σ`, sends an exponent `m` to
`E (σ.inv ≫ E.symm m)`. Thus it is precisely the published inverse-precomposition
character action, transported through the character/exponent identification.
`exponentValue_inv_universalPoint` proves that evaluating the character with
exponent `m` on the universal point followed by `σ.inv` gives the monomial with
exponent `exponentAut I σ m`. Its proof uses the published character evaluation
comparison, composition law and universal-point evaluation.

The weight matrix `P_m` is the published coefficient matrix
`CharacterRestrictionFiniteIndex.weight ρ I j m`.
`coeff_inv_universalPoint` applies the published finite representation evaluation
formula to the transformed universal point. Injectivity of `exponentAut` makes
the coefficient at its image of `m` a Kronecker delta, whose sum is `P_m`.

`baseMatrix ρ n` constructs the invertible representation matrix of a point
`n ∈ G(Spec k)`, using its constant pullback to the canonical affine test algebra
`k`. `constantPoint_matrix_apply` shows that its pullback to the group-algebra
test ring has constant entries: each is the monomial of exponent zero with the
original entry as coefficient. This follows from constant-point naturality and
the naturality of the published general-linear point equivalence.

Suppose `n` normalizes `j` through `σ`, and write `M = baseMatrix ρ n` and
`a = exponentAut I σ`. On the universal torus point `t`, the defining normalizer
equation gives
`j(t) = n * j(σ.inv(t)) * n⁻¹`.
Applying the representation and multiplying by `M` gives the matrix equation
`A(t) * M = M * A(σ.inv(t))`.
`weight_mul_baseMatrix` extracts the coefficient at `a(m)`, using the two
coefficient comparisons above, and proves
`P_(a(m)) * M = M * P_m`.

Finally, `weight_ne_zero_exponentAut` proves that `P_m ≠ 0` implies
`P_(a(m)) ≠ 0`: if the latter vanished, multiplication on the left by the
actual inverse of `M` would force `P_m = 0`.
`weight_ne_zero_normalizingAut` specializes this to the chosen automorphism
of every actual base normalizer point. The same assertion applies to the inverse
normalizer point, so this supplies the forward stability premise used by a
group action on the finite nonzero weight set.

The provenance is entirely internal: this module combines the published
`Torus.Maximal` normalizer and character-action definitions,
`Torus.WeightDecomposition` character evaluation comparisons, and
`Rational.CharacterRestrictionFiniteIndex` universal matrices, weight matrices
and finite evaluation formula. It asserts no additional literature theorem.
Full Weyl-image finiteness and the final central-isogeny root-datum theorem
remain separate obligations.
