# The product of the cyclic coordinates is a determinant

Lean module: `Langlands.Representation.AffineGeneric.Determinant`, namespace
`Langlands.AffineGeneric`.

Let `F` be a field with a valuative relation, `𝔄` the standard Iwahori order and `𝔓` its
radical in `M_{m+1}(F)`, and `ρ = finRotate (m + 1)`. For `ϖ : Fˣ`, write
`aᵢ(Y) = coord ϖ Y i` as in `Radical`.

## Residues and conjugation

- `IsIwahoriOrder.resOf_det`: for `A ∈ 𝔄`, `res(det A) = ∏ᵢ res(Aᵢᵢ)`. Viewing `A` over `𝒪`,
  the residue of `det A` is the determinant of the reduction of `A` (`RingHom.map_det`), which
  is upper triangular over `k` (`Matrix.det_of_isUpperTriangular`).
- `prod_weight`: `∏ᵢ weight ϖ i = ϖ⁻¹`. `finRotate_symm_zero`: `ρ⁻¹ 0 = last`.
- `coordProd ϖ g` defines `D(g) = ∏ᵢ aᵢ(g - 1)`.
- `det_conj_sub_one`: `det(x⁻¹ g x - 1) = det(g - 1)`.

## Determinant identity

Assume `ϖ` is a uniformizer (`Iwasawa.IsUniformizingElement`).

- `isIwahoriOrder_rotate`: for `Y ∈ 𝔓`, the matrix `A` with rows
  `A i = weight ϖ (ρ⁻¹ i) · Y (ρ⁻¹ i)` lies in `𝔄`. Row `0` of `A` is `ϖ⁻¹` times the last row of
  `Y`, which is integral; for `i ≠ 0`, row `i` of `A` is row `i - 1` of `Y`.
- `prod_coord` (**determinant identity**): for `Y ∈ 𝔓`,
  `∏ᵢ aᵢ(Y) = res((-1)^m ϖ⁻¹ det Y)`. The diagonal entries of `A` have residues `a_{ρ⁻¹ i}(Y)`,
  and `det A = sign(ρ) ϖ⁻¹ det Y = (-1)^m ϖ⁻¹ det Y` (`Matrix.det_mul_column`,
  `Matrix.det_permute`, `sign_finRotate`); now apply `IsIwahoriOrder.resOf_det` to `A`.
- `coordProd_eq`: for `g ∈ I⁺`, `D(g) = res((-1)^m ϖ⁻¹ det(g - 1))`.
- `coordProd_conj`: if `g` and `x⁻¹ g x` both lie in `I⁺`, then `D(x⁻¹ g x) = D(g)`.

The identity `prod_coord` is a direct computation.
