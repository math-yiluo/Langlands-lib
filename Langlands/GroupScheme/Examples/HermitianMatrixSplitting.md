# Splitting the determinant-one isometries of a Hermitian matrix

Author: Worker 5375.

This internal module is pure algebra. It shows that the determinant-one isometries of a
Hermitian matrix become `SL` once the quadratic extension splits. It contains no scheme
theory. It is the matrix step of the descent argument for Task 6209
(`OuterTypeAHermitianPresentationStatement`): over a field `M` containing `L`, it
identifies the points of `SU(H)` with points of `SL`.

Write `Mᴴ = adjoint c M = (c̄ M)ᵀ`. The published `HermitianMatrix` interface defines:
- `Form c Ix`: an invertible Gram matrix `H.gram` with `H.gramᴴ = H.gram`;
- `Preserves H M`: `Mᴴ · H.gram · M = H.gram`;
- `specialUnitarySubgroup H`: the matrices in `GL_Ix(A)` that preserve `H` and have
  determinant `1`.

## Abstract splitting (section `Abstract`, namespace `Langlands.GroupScheme.HermitianMatrix`)

The setting:
- `A` and `R` are commutative rings in arbitrary universes, and `c` is a ring involution
  of `A`.
- `Ix` is a finite index type with decidable equality, and `H : Form c Ix`.
- `p, q : A →+* R` are ring maps with `q = p ∘ c̄` (hypothesis `hpq`).

The results:
- `specialUnitary_det` and `specialUnitary_preserves` unpack membership in
  `specialUnitarySubgroup H`.
- `adjoint_map_left`: `p(Mᴴ) = q(M)ᵀ`, which uses only `hpq`. `adjoint_map_right`:
  `q(Mᴴ) = p(M)ᵀ`, which also uses `c̄ ∘ c̄ = id`. Here `p(M)` means `p` applied to
  every entry.
- `gram_map_right`: `q(H.gram) = p(H.gram)ᵀ`, from Hermitian symmetry.
- `gram_inv_map_mul` and `gram_map_mul_inv`: `p(H.gram⁻¹)` and `p(H.gram)` are mutually
  inverse.
- `splitSL H p : specialUnitarySubgroup H →* SL_Ix(R)` applies `p` to every entry.
  `coe_splitSL` states its matrix.
- `splitSL_conj`: for `x` in `specialUnitarySubgroup H`,
  `p(H.gram⁻¹) · (q(x)⁻¹)ᵀ · p(H.gram) = p(x)`. The proof applies `p` to the isometry
  equation `xᴴ H x = H` and uses `adjoint_map_left`. This gives
  `q(x)ᵀ p(H) p(x) = p(H)`, and the claim follows by cancelling.
  In the descent step, this identity turns the outer cocycle formula into a statement
  about `p`-coordinates.

Two hypotheses on `(p, q)` are used:
- `hinj`: `p` and `q` are jointly injective;
- `hsurj`: every pair `(r, s)` of elements of `R` is `(p a, q a)` for some `a`.

The results under these hypotheses:
- `matrix_eq_of_maps`: under `hinj`, a matrix over `A` is determined by its images along
  `p` and `q`.
- `splitSL_injective` (assumes `hinj`): by `splitSL_conj`, `p(x)` determines `q(x)`. Then
  `matrix_eq_of_maps` gives `x`.
- `splitSL_surjective` (assumes `hinj` and `hsurj`): let `s ∈ SL_Ix(R)`. Put
  `t = (p(H) · s⁻¹ · p(H⁻¹))ᵀ`, which has determinant `1`. Choose `x` entrywise with
  `p(x) = s` and `q(x) = t`. Joint injectivity then gives `det x = 1` and `xᴴ H x = H`.
  To check the second equation, apply `p` and `q`, using `adjoint_map_left`,
  `adjoint_map_right` and `gram_map_right`.
- `splitEquiv H p q hpq hinj hsurj : specialUnitarySubgroup H ≃* SL_Ix(R)` is
  `splitSL H p` as a group isomorphism. `coe_splitEquiv` states that its matrix is
  `p(x)`.

## The tensor-product case (section `Tensor`)

Here `K` and `L` are fields in one universe `u` with `L/K` separable quadratic, in any
characteristic. `R` is a commutative `K`-algebra in universe `u`, and
`conjugation K L` is the nonidentity `K`-automorphism of `L` from the published
`SU3RootParametersQuadratic`.

- `tensorProj K L φ : L ⊗_K R →ₐ[K] R` sends `ℓ ⊗ r` to `φ(ℓ) r`, for a `K`-algebra map
  `φ : L →ₐ[K] R`. It is Mathlib's `Algebra.TensorProduct.productMap φ id`, and
  `tensorProj_tmul` states its value on pure tensors.
- `tensorProj_scalarConjugation`: the projection for `φ ∘ conjugation` equals the
  projection for `φ` after the published `QuasiSplitUnitary.scalarConjugation`
  (`ℓ ⊗ r ↦ c(ℓ) ⊗ r`).
- `tensorProj_bijective`: `x ↦ (tensorProj φ x, tensorProj (φ ∘ conjugation) x)` is a
  bijection `L ⊗_K R → R × R`. The proof makes `R` an `L`-algebra through `φ`. It then
  identifies the map with the published isomorphism
  `QuasiSplitUnitary.tensorSplit R (conjugation K L)`, which sends `ℓ ⊗ r` to
  `(ℓ r, c(ℓ) r)`, and checks agreement on pure tensors.
- `tensorProj_injective₂` and `tensorProj_surjective₂` restate this bijectivity as the
  hypotheses `hinj` and `hsurj` of the abstract section.

## Provenance and scope

The provenance is internal. The algebra is the standard fact that a unitary group splits
as a general linear group over a split quadratic algebra: `L ⊗_K R ≅ R × R` when `L`
embeds in `R`. It is formulated here for an arbitrary nonsingular Hermitian Gram matrix
and arbitrary coordinate maps `(p, q)`. The tensor section reuses the published
splitting `QuasiSplitUnitary.tensorSplit`. The module claims nothing about group
schemes. Combining this splitting with a point model of `SU(H)` is left to the descent
module.
