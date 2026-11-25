# Adic algebraization in native Hopf-point coordinates

This module adapts the published `HopfPointExtension.IsHopfPoint` interface to
the coefficient-level adic algebraization construction. It is an internal
interface for SGA 3, Exposé IX, Theorem 7.1, recomposed pp.56–58 (original
margins pp.68–72), registered source `sga3-expose-ix-gille-polo-2009`,
SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The source works with compatible Hopf maps; this adapter uses the existing
Library point coordinates so that the scheme-level consumer can reuse its
published naturality theorems.

Let `C` be a commutative `A`-bialgebra, `Q` a commutative `A`-algebra, and
`M` a commutative additive group. `inl_mul_inr` identifies the product of
the two group-algebra inclusions in `Q[M × M]` with the tensor-coordinate
map `Q[M] ⊗[Q] Q[M] ≃ₗ[Q] Q[M × M]`. The proof is induction on finite
coefficient families. Tensor induction then proves `pairMap_coeff`:
the published pair map's coefficients are the coefficient pairings of
`AdicDiagonalAlgebraization`. `diagMap_coeff` computes its diagonal
counterpart. `groupCounit_eq` identifies the published group-algebra
counit with the standard coalgebra counit, again by finite-family induction.

Thus a published Hopf point supplies the exact diagonal and counit equations
used by `AdicGroupAlgebra`: the lemmas `diagonal` and `counit` obtain them
by evaluating the Hopf-point equalities on each source element and coefficient.
No extra coefficient equations are assumed.

For an ideal `I`, `System I` stores compatible `A`-algebra maps
`C →ₐ[A] (A/Iⁿ)[M]`, their native Hopf-point proofs, and agreement of
coefficients under every quotient map for `n ≤ k`. `System.toAlgebraSystem`
forgets to the preceding coefficient interface. If `A` is noetherian and
`I`-adically complete and separated, `System.lift` is the actual bialgebra
map `C →ₐc[A] A[M]`. `reduce_lift` identifies each quotient, and
`lift_unique` proves uniqueness among bialgebra maps with those quotients.

`System.ofSucc` accepts maps over `A/I^(n+1)` with only successive
coefficient agreement. It inserts the unique algebra map to the zero
quotient's group algebra; its Hopf-point equations hold since the coefficient
ring is zero. The factor-map transitivity theorem extends compatibility to
all index pairs. `ofSucc_map` identifies the positive-power maps exactly.

The ring, source algebra and character group have independent universes.
No finite generation condition on `C` or `M`, or smoothness or flatness
condition, is used. This module supplies an algebraic adapter; the actual
scheme-level construction is in `HomScheme.AdicDiagonalizable`.
