# The isometry group of a bilinear form; the standard symplectic form

**GKT chapter 2** (the symplectic group `Sp(W) = {g ∈ GL(W) : ⟨gw, gw'⟩ = ⟨w, w'⟩}`, p. 47).

The module `Langlands.LinearAlgebra.Symplectic` defines the group of linear automorphisms of a module
preserving a bilinear form, the standard symplectic form on `l ⊕ l → R`, and identifies Mathlib's
group of symplectic matrices with the isometry group of that form.

## Content

Let `R` be a commutative ring, `W` an `R`-module and `B : LinearMap.BilinForm R W`.

- `LinearMap.BilinForm.isometryGroup B : Subgroup (W ≃ₗ[R] W)`, the `g` with
  `B (g x) (g y) = B x y` for all `x`, `y` (`mem_isometryGroup_iff`, `isometryGroup_apply`); the
  product is composition (`coe_mul_apply`, `coe_one_apply`). For an alternating non-degenerate
  form on a vector space over a field this is the book's `Sp(W)`; nothing here assumes it. (The
  name is in the name space `Langlands.LinearMap.BilinForm`, so it is written
  `LinearMap.BilinForm.isometryGroup B` rather than with dot notation.)
- `stdSymplecticForm l R`: the form
  `ω(w, w') = ∑ᵢ (w (inl i) w' (inr i) - w (inr i) w' (inl i))` on `l ⊕ l → R`
  (`stdSymplecticForm_apply_eq_sum`), equal to `-(w ⬝ᵥ J *ᵥ w')` for Mathlib's `Matrix.J`
  (`stdSymplecticForm_apply`).
- Symplectic matrices preserve it (`stdSymplecticForm_mulVec`), and a matrix whose action preserves
  it is symplectic (`mem_symplecticGroup_of_stdSymplecticForm`: `Aᵀ J A = J` is read off on the
  standard basis, and `Aᵀ J A = J` gives `A J Aᵀ = J` by Mathlib's `SymplecticGroup.transpose_mem`).
- `Matrix.symplecticGroup.toLinearEquiv g : (l ⊕ l → R) ≃ₗ[R] (l ⊕ l → R)`, `w ↦ g *ᵥ w`;
  `Matrix.symplecticGroup.toIsometryGroupHom l R` and the isomorphism
  `Matrix.symplecticGroup.toIsometryGroup l R :
  Matrix.symplecticGroup l R ≃* isometryGroup (stdSymplecticForm l R)`
  (`toIsometryGroup_apply`: `g` acts by `w ↦ g *ᵥ w`), bijective because a linear map of
  `l ⊕ l → R` is given by its matrix (`LinearMap.toMatrix'`).

The isometry group acts on the Heisenberg group (`HeisenbergGroup.isometryAction`,
`Langlands/Theta/Heisenberg/Basic.lean`); `stdSymplecticForm l ℝ` is the form of the real branch
(`Langlands/Theta/Real/`).

## Declarations

- `Langlands.LinearMap.BilinForm.isometryGroup`, `mem_isometryGroup_iff`, `isometryGroup_apply`,
  `coe_mul_apply`, `coe_one_apply`.
- `Langlands.stdSymplecticForm`, `stdSymplecticForm_apply_eq_sum`, `stdSymplecticForm_apply`,
  `stdSymplecticForm_mulVec`, `mem_symplecticGroup_of_stdSymplecticForm`.
- `Langlands.Matrix.symplecticGroup.toLinearEquiv`, `toIsometryGroupHom`,
  `toIsometryGroupHom_bijective`, `toIsometryGroup`, `toIsometryGroup_apply`.

## Dependencies

Mathlib: `LinearAlgebra.BilinearForm.Properties`, `LinearAlgebra.Matrix.ToLin`,
`LinearAlgebra.SymplecticGroup`.
