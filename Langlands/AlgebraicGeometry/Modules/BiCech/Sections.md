# Sections of the bi-Čech complex and their local exactness

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.Sections`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

## Data

- `BiCover P` bundles schemes `X`, `Y`, morphisms `f : P ⟶ X`, `g : P ⟶ Y`, and ordered
  affine covers `𝒰` of `X` and `𝒱` of `Y`.
- `biOpen 𝒲 s t = f⁻¹(𝒰.inter s) ⊓ g⁻¹(𝒱.inter t)`.
- `bo 𝒲 V s t` is the open `(biOpen s t).ι ''ᵁ ((biOpen s t).ι ⁻¹ᵁ V)`. It equals
  `biOpen s t ⊓ V` (`bo_eq`), and its sections are the sections of
  `CechResolution.sheafOn F (biOpen s t)` over `V`.
- `rowFam 𝒲 V t` and `colFam 𝒲 V s` are the families of opens of
  `BiCech.OneDirection` with `t`, respectively `s`, held fixed.
- `B 𝒲 F p q V = ∀ s t, F(bo V s t)` is the `(p, q)`-term of the double complex of
  sections over `V`.

## Double and total complex

- `δ₁` and `δ₂` are the alternating Čech differentials in `s` and in `t`. Each is the
  one-direction `δ` applied to a row or a column. Both square to zero (`δ₁_δ₁`,
  `δ₂_δ₂`), and they commute (`δ₁_δ₂`). The lemmas `δ₁_eq_zero_of_const` and
  `δ₂_eq_zero_of_const` state that a degree-zero family obtained by restriction from a
  family independent of the other index is killed.
- `TSec 𝒲 F n V = ∀ p q, p + q = n → B 𝒲 F p q V` is the degree-`n` term of the total
  complex.
- `DT` is the total differential `δ₁ + (-1)^p δ₂`. On the component of bidegree `(p, q)`
  it is defined by matching on `p` and `q` through `horT` and `verT`. Its values are given
  by `DT_zero_succ`, `DT_succ_zero` and `DT_succ_succ`. `DT_DT` states that
  `DT (DT c) = 0`, componentwise.
- `augT m` is the family of restrictions of a section `m ∈ F(V)`, and `DT_augT` states
  that `DT (augT m) = 0`.

## Local exactness

Let `V ⊆ f⁻¹(𝒰.U a) ∩ g⁻¹(𝒱.U b)`. Then the row families are stable under inserting `a`
(`insStable_row`) and the column families under inserting `b` (`insStable_col`). This
gives the contractions `contr₁` and `contr₂` and the projection `proj₁`. The lemmas
`contr₁_δ₂` and `proj₁_δ₂` show that these commute with `δ₂`, and `δ₁_proj₁` shows that
`proj₁` is killed by `δ₁`.

- `preimT hV hV' c` is the family whose `(p + 1, q)`-component is `contr₁ c_{p+2,q}`, and
  whose `(0, q)`-component is `contr₁ c_{1,q} + proj₁ (contr₂ c_{0,q+1})`.
- `DT_preimT`: if `DT c = 0` in degree `n + 1`, then `DT (preimT c) = c`.
- `augT_eq_of_DT_eq_zero`: a degree-zero cocycle is `augT m`, where `m` is the
  `((a), (b))`-component restricted to `V`.

The proof of `DT_preimT` uses the full row homotopy identities of `BiCech.OneDirection`,
the commutation of `contr₁` with `δ₂`, and the cocycle relations of `c` in bidegrees
`(p + 2, q)`, `(1, q + 1)` and `(0, q + 2)`. The degree-zero statement uses the row and
column projection identities.

Provenance: internal. This is the standard argument that the augmented total complex of a
double complex with contractible augmented rows and column is exact. It is written out
explicitly for the bi-Čech complex.
