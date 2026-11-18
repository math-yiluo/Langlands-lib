# Additivity of the Tits class on dominant star-fixed weights

This module proves the additivity of the Tits algebra: for dominant
star-fixed weights `λ` and `μ`, the Tits algebra of the irreducible
representation of highest weight `λ + μ` is Brauer equivalent to the tensor
product of the Tits algebras of the irreducible representations of highest
weights `λ` and `μ`. Throughout, "`ρ` of highest weight `λ`" means the
published predicate `IsHighestWeight ρ λ`, which includes irreducibility. This follows the proof of Corollary 3.5 of Tits,
*Représentations linéaires irréductibles d'un groupe réductif sur un corps
quelconque*, J. reine angew. Math. 247 (1971), p. 205: Proposition 3.4
(pp. 204–205) is applied to `V(λ) ⊗ V(μ)` and its subquotient of highest
weight `λ + μ`. The matrix-coordinate implementation (adapted idempotents,
compressions, corners) is this development's own. The argument works over any field `k`,
in any characteristic, and for any Galois extension `K/k` carrying a Galois
pinning. No inner-type hypothesis is used.

The highest-weight input is the published
`splitHighestWeightClassification`, used through `Reductive/TitsDominantClass`;
no classification hypothesis appears in the statements.

## Declarations

### Tensor products and Galois twists (`MatrixRepresentation`)

- `universalMatrix_tensor_eq_kronecker`: the universal matrix of `ρ ⊗ τ` is
  the Kronecker product of the universal matrices (`universalMatrix_tensor`).
- `Intertwines.kronecker`: if `C₁ : ρ₁ → τ₁` and `C₂ : ρ₂ → τ₂` intertwine,
  then `C₁ ⊗ C₂ : ρ₁ ⊗ ρ₂ → τ₁ ⊗ τ₂` intertwines. The proof uses the
  universal-matrix criterion `intertwines_iff_universalMatrix` and the
  mixed-product rule `Matrix.mul_kronecker_mul`.
- `Intertwines.of_universalMatrix_eq`: intertwining depends only on the
  universal matrix of the target.
- `universalMatrix_galoisTwist_tensor`: `(ρ ⊗ τ)^σ` and `ρ^σ ⊗ τ^σ` have the
  same universal matrix. Both are the entrywise image of the Kronecker
  product under the ring map `σ ⊗ id` (`universalMatrix_galoisTwist`).
- `intertwines_galoisTwist_tensor`: if `P : ρ → ρ^σ` and `Q : τ → τ^σ`
  intertwine, then `P ⊗ Q : ρ ⊗ τ → (ρ ⊗ τ)^σ` intertwines.

### Additivity (`GaloisPinningData`)

- `isStarFixedWeight_add`: star-fixed weights are closed under addition,
  because each `weightEquiv` is additive.
- `titsCSAOf_add_isBrauerEquivalent`: let `ρ₁`, `ρ₂` and `ρ` have highest
  weights `λ`, `μ` and `λ + μ`, with `λ` and `μ` star-fixed. Then
  `titsCSAOf ρ` is Brauer equivalent to
  `Langlands.Brauer.tensor (titsCSAOf ρ₁) (titsCSAOf ρ₂)`. The proof:
  1. Let `P₁ σ`, `P₂ σ` be the Galois intertwiners chosen in `titsCSAOf`, and
     `P σ = P₁ σ ⊗ P₂ σ`. This is an invertible intertwiner
     `T → T^σ` for `T = ρ₁ ⊗ ρ₂` (`intertwines_galoisTwist_tensor`,
     `isUnit_kronecker`).
  2. `B` is the image of the Kronecker map on
     `titsAlgebra ρ₁ ⊗ titsAlgebra ρ₂`. It is twisted-fixed for `P`, its
     `K`-span is everything, and it contains `titsAlgebra T`
     (`range_kroneckerTensor_le_twistedFixed`, `span_range_kroneckerTensor`,
     `titsAlgebra_tensor_le`).
  3. The flag `Y = highestRadical T (λ+μ) ≤ X = highestGenerated T (λ+μ)` is
     twisted-stable for `P` (`isTwistedStable_highestGenerated`,
     `isTwistedStable_highestRadical`). So `exists_adapted_idempotent` gives
     `f ∈ B` that is idempotent, has image in `X`, kills `Y` and is the
     identity modulo `Y` on `X`.
  4. `nonempty_highestSubquotientData` gives coordinates `D` of the
     subquotient `X/Y`. `HighestSubquotientData.isHighestWeight` shows that
     it has highest weight `λ + μ`. Its inputs are multiplicity one of
     `λ + μ` and maximality (`finrank_representationWeightSpace_tensor_add`,
     `sub_mem_positiveRootMonoid_tensor`).
  5. `titsAlgebra_quot_eq_compressed` identifies `titsAlgebra D.quot` with
     `compressed B F E`, where `F = proj · retr · f` and `E = f · incl · sect`.
  6. The chain of Brauer equivalences:
     - `titsCSAOf ρ ~ titsCSAOf D.quot` by `titsCSAOf_isBrauerEquivalent`,
       since both have highest weight `λ + μ`;
     - `titsCSAOf D.quot ~ toCSA (compressed B F E)`, by equality of the
       carriers (`Subalgebra.equivOfEq`);
     - `toCSA (compressed B F E) ~ toCSA P B` by the corner theorem
       `isBrauerEquivalent_toCSA_compressed`;
     - `toCSA P B = kroneckerCSA … ~ tensor (titsCSAOf ρ₁) (titsCSAOf ρ₂)`
       by `kroneckerCSA_isBrauerEquivalent`.

### Packaged statement (`Langlands.GroupScheme`)

- `TitsAdditivityStatement` quantifies the conclusion of
  `titsCSAOf_add_isBrauerEquivalent` over all Galois extensions `K/k`
  (`IsGalois k K`), affine `G` locally of finite type over `k`, Galois
  pinnings `d`, representations `ρ₁`, `ρ₂`,
  `ρ` on `Fin n₁`, `Fin n₂`, `Fin r` with `IsHighestWeight` for `λ`, `μ`,
  `λ + μ` respectively (so each is irreducible),
  and star-fixed `λ`, `μ`.
- `titsAdditivity` proves it.
