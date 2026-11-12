# The normalized path basis and rational representation matrices

This is an internal derived linear algebra interface for the path representations used in the even-chain cross-section proof. It introduces no new representation-theoretic assumption or unproved statement. Its inputs are the published path-weight decomposition and normalized path vectors from `PathFundamentalWeights` and `PathReflectionScalars`, together with Mathlib's basis and characteristic-polynomial constructions.

Let `k` be any field, `p` a split pinning of an affine group scheme `G` over `k`, `β : Fin L → p.base.support` a path component, and `ρ` a highest-weight matrix representation with path-fundamental highest weight `lam`. Supply normalized simple-root maps `x` and a nonzero vector `v₀` on the initial path-weight line. The matrix coordinate type of `ρ` is any finite decidable type `d : Type`; the construction is polymorphic in the field universe.

`linearIndependent_normalizedPathVector` proves that the vectors with indices `Fin (L + 1)` are linearly independent: distinct indices give distinct path weights, the corresponding weight spaces are independent, and every normalized vector is nonzero. The path representation has dimension `L + 1`, so `normalizedPathBasis` extends this family to a basis without changing its vectors. The lemma `normalizedPathBasis_apply` identifies its vectors with the supplied normalized family.

`normalizedPathMatrix` is the monoid homomorphism from actual rational points of `G` to square matrices obtained from `ρ.rationalMatrix` by changing to this basis. Its entry formula `normalizedPathMatrix_apply` evaluates the basis coordinate of the action on a normalized path vector. The proof of `charpoly_normalizedPathMatrix` applies Mathlib's characteristic-polynomial invariance under conversion between matrices and endomorphisms, showing that this change of basis preserves the entire characteristic polynomial.

This module packages existing mathematics for later explicit matrix calculations. It makes no assertion about the modified products or the canonical class quotient.
