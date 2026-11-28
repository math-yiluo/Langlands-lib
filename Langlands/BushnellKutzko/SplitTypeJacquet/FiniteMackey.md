# Mackey vanishing along a lower corner

Module `Langlands.BushnellKutzko.SplitTypeJacquet.FiniteMackey`. Finite-group input for the
Jacquet nonvanishing of inhomogeneous level-zero types.

## Coarse blocks and lower corners

For a block shape `B` of `n` and a cut `j`, `InFirst B j a` says that the coordinate `a` lies
in one of the first `j` blocks, and `coarseBlock B j` is the two-valued block function (`0` on
the first `j` blocks, `1` on the others). `blockTriangular_of_mem_parabolic`: elements of the
standard block parabolic `B.parabolic k` are block upper triangular for `coarseBlock B j`;
`blockTriangular_permutation`: so is the permutation matrix of a permutation preserving the
first `j` blocks.

`Corner B j k` is the space of matrices with rows outside and columns inside the first `j`
blocks; `cornerMatrix` places such a matrix in `Matrix (Fin n) (Fin n) k`, and corners multiply
to zero (`cornerMatrix_mul`). `lowerUnip X = 1 + cornerMatrix X` is invertible with inverse
`lowerUnip (-X)`, and `lowerUnip (X + Y) = lowerUnip X * lowerUnip Y`.
`eq_zero_of_blockTriangular_lowerUnip`: a lower corner unipotent that is coarse upper triangular
is the identity.

## Mackey vanishing

For a finite field `k` and a Harish–Chandra datum `E` (a block shape with an irreducible
cuspidal class in each block), `parabolicRep E` is the Levi tensor `E.leviRep` inflated to the
standard parabolic `P`.

`mackey_lowerCorner_eq_zero`: suppose no block among the first `j` carries the label of a block
after them. If `X ≠ 0` and `T : E.leviRep → E.leviRep` satisfies
`T ∘ λ(q) = λ(x q x⁻¹) ∘ T` for every `q ∈ P` with `x q x⁻¹ ∈ P`, where `x = lowerUnip X`, then
`T = 0`. Proof: write `x⁻¹ = p₁ w' p₂` with `w'` the inverse permutation matrix of the minimal
representative `w` of the double coset `P x⁻¹ P` (`parabolicDoubleCoset_bijective`). The map
`T' = λ(p₂) ∘ T ∘ λ(p₁)` is a nonzero element of the Mackey intertwining space at `w'`, so the
Harish–Chandra Mackey term at `w` is nonzero. By `conjugatesLevi_of_mackeyTerm_ne_zero` and
`harishChandraMackeyTerm_eq_ite`, `w` conjugates the Levi onto itself matching every block label;
by the label hypothesis it preserves the first `j` blocks. Then `x⁻¹ = p₁ w' p₂` is coarse upper
triangular, which forces `X = 0`.

## Retractions

`exists_equivariant_leftInverse` (Maschke averaging): an injective equivariant linear map
between complex representations of a finite group has an equivariant linear left inverse,
namely the average `|H|⁻¹ ∑ σ(h⁻¹) ∘ φ ∘ τ(h)` of any linear left inverse `φ`.

`retraction_lowerUnip_eq_zero`: let `τ` be a representation of `GL_n(k)`, `f` a
`P`-equivariant map from `λ` into `τ` and `ψ` a `P`-equivariant map back. Under the same label
hypothesis, `ψ ∘ τ(lowerUnip Y) ∘ f = 0` for every nonzero corner `Y`; the composite satisfies
the twisted equivariance of `mackey_lowerCorner_eq_zero`.
