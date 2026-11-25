# `U(ν, ν)` and `U(Q)` as isometry groups of `ε`-Hermitian spaces

**GKT §4.4.1** (the Siegel parabolic `P(X) = M(X) ⋉ N(X)`, `m(a)`, `n(b)`, p. 114; the Weyl
elements `w_S` of a standard basis, (4.8), p. 115) and Definition 4.8 (standard bases, p. 98), read
on the matrix groups of `Langlands.Group.Unitary.Basic` and `Langlands.Group.Unitary.Hyperbolic`.

The module `Langlands.Group.Unitary.Classical` identifies the Library's quasi-split unitary group
`U(ν, ν) = ofForm c (hyperbolicForm ν E)` with the isometry group of a split skew-Hermitian space in
the sense of `Langlands.LinearAlgebra.EpsilonHermitian.Basic`, and its Siegel parabolic, Levi
elements, unipotent elements and Weyl element with the objects of
`Langlands.Group.Classical.SiegelParabolic`; and `U(Q) = ofForm c Q` with the isometry group of the
Hermitian space of `Q`.

## Setting

`E` is a field, `c : E →ₐ[F] E` with `hc : Function.Involutive c`; `ringInvo c hc` is `c` as a
`RingInvo E` (`conj_ringInvo`).

## Content

- `hyperbolicHermitianForm c hc ν : EpsilonHermitianForm (ringInvo c hc) (-1) (ν ⊕ ν → E)`:
  `h(u, v) = u J c(v)ᵀ` on row vectors, `J = [[0, 1], [-1, 0]]`; `h(εₐ, ε_b) = J_{ab}`
  (`hyperbolicHermitianForm_single`) and `h(u M, v M) = u (M J c(M)ᵀ) c(v)ᵀ`
  (`hyperbolicHermitianForm_vecMul`).
- `hyperbolicStandardBasis c hc ν`: the standard basis `eᵢ = (0, εᵢ)`, `eᵢ* = -(εᵢ, 0)`
  (`hyperbolicStandardBasis_fst`, `_snd`); `X = span {eᵢ}` is the space of rows `(0, y)`
  (`mem_lagrangianFst_iff`), `Y = span {eᵢ*}` that of rows `(x, 0)` (`mem_lagrangianSnd_iff`).
- `toIsometryGroup c hc : U(ν, ν) ≃* U(W)`, `g ↦ (w ↦ w g⁻¹)` (`toIsometryGroup_apply`): a
  homomorphism into the isometry group because `g⁻¹ J c(g⁻¹)ᵀ = J`
  (`mem_ofForm_hyperbolicForm_iff`); bijective because an isometry is `w ↦ w M` for the matrix `M`
  of its values on the unit rows, with `M J c(M)ᵀ = J` (`mul_hyperbolicForm_mul_apply`).
- `toIsometryGroup_mem_siegelParabolic_iff`: `g` lies in the Library's Siegel parabolic (lower left
  block zero) iff its image lies in `P(X)`.
- `restrictLagrangianFst c hc hp` (`p|_X`), `lagrangianFstBasis c hc ν` (the basis `(eᵢ)` of `X`,
  coordinates `lagrangianFstBasis_repr`), `toMatrix_restrictLagrangianFst`: the matrix of `p|_X` is
  `((p⁻¹)₂₂)ᵀ`; `det_restrictLagrangianFst`: `det(p|_X) = det (p⁻¹)₂₂`.
- `toIsometryGroup_siegelLevi`: `diag(a, c(a)⁻ᵀ)` is `m(a')` (`siegelLeviOf`), `a'` the automorphism
  of `X` with matrix `c(a)` in `(eᵢ)`; `toIsometryGroup_siegelLevi_mem`: it lies in `M(X) =
  P(X) ∩ P(Y)`.
- `toIsometryGroup_siegelUnipotent_mem`: `[[1, b], [0, 1]]` lies in `N(X)`;
  `exists_toIsometryGroup_siegelUnipotent`: it is `n(b')` (`siegelUnipotentOf`) with
  `b'(eⱼ*) = ∑ₖ b_{jk} eₖ`.
- `siegelLevi_one`, `siegelUnipotent_zero`; `toIsometryGroup_mem_siegelUnipotent_iff`: the image of
  `g` lies in `N(X)` iff `g = [[1, b], [0, 1]]` (from `P = M ⋉ N`, an element `m(a)` of `N(X)` fixes
  `X`, so `c(a)ᵀ = 1`); `toIsometryGroup_mem_siegelLevi_iff`: the image of `g` lies in
  `M(X) = P(X) ∩ P(Y)` iff `g = diag(a, c(a)⁻ᵀ)` (an `n(b)` stabilizing `Y` has `b = 0`).
- `idempotentOf ν S`, the diagonal idempotent of `S ⊆ ν`, and `partialWeylElement c S =
  [[1 - e_S, e_S], [-e_S, 1 - e_S]] ∈ U(ν, ν)` (`partialWeylElement_val`, `_inv_val`);
  `partialWeylElement_univ`: `w_ν` is the Library's `weylElement c ν`;
  `toIsometryGroup_partialWeylElement`: **it is the Weyl element `w_S` of the standard basis**
  (`eᵢ ↦ -eᵢ*`, `eᵢ* ↦ eᵢ` for `i ∈ S`, GKT (4.8) with `ε = +`); `toIsometryGroup_weylElement`.
- `blockIndexEquiv σ`, `blockMatrix σ A B` (`diag(A, B)` written in the coordinates of `ν` for
  `σ : ν₁ ⊕ ν₂ ≃ ν`) with `blockMatrix_mul`, `blockMatrix_one`, `transpose_blockMatrix`,
  `map_blockMatrix`, `blockMatrix_hyperbolicForm`, `toBlocks₂₁_blockMatrix`,
  `toBlocks₂₂_blockMatrix`, `det_toBlocks₂₂_blockMatrix`; **`blockEmbedding c σ : U(ν₁, ν₁) ×
  U(ν₂, ν₂) →* U(ν, ν)`** (the book's `U(W₁) × U(W₂) ⊆ U(W₁ ⊕ W₂)`, `blockEmbedding_val`), mapping
  `P₁ × P₂` into `P` (`blockEmbedding_mem_siegelParabolic`);
  `partialWeylElement_eq_blockEmbedding`: `w_S` is the image of `(w, 1)` for `S ⊕ Sᶜ ≃ ν`.
- `hermitianFormOf c hc Q hQ : EpsilonHermitianForm (ringInvo c hc) 1 (α → E)`,
  `(u, v) ↦ uᵀ Q c(v)` for a Hermitian `Q`; `mulVecEquiv`, `toIsometryGroupOfForm c hc hQ :
  U(Q) →* U(V)`, `h ↦ (v ↦ h v)`, injective (`toIsometryGroupOfForm_injective`).

## Declarations

`ringInvo`, `conj_ringInvo`, `hyperbolicHermitianForm`, `hyperbolicHermitianForm_apply`,
`hyperbolicHermitianForm_single`, `hyperbolicHermitianForm_vecMul`, `mul_hyperbolicForm_mul_apply`,
`hyperbolicBasis`, `hyperbolicBasis_inl`, `hyperbolicBasis_inr`, `hyperbolicStandardBasis`,
`hyperbolicStandardBasis_basis`, `hyperbolicStandardBasis_fst`, `hyperbolicStandardBasis_snd`,
`rowMulInvEquiv`, `rowMulInvEquiv_apply`, `rowMulInvEquiv_mem`, `toIsometryGroupHom`,
`toIsometryGroupHom_bijective`, `toIsometryGroup`, `toIsometryGroup_apply`,
`mem_lagrangianFst_iff`, `mem_lagrangianSnd_iff`, `vecMul_fromBlocks_inl`, `vecMul_fromBlocks_inr`,
`toIsometryGroup_mem_siegelParabolic_iff`, `idempotentOf`, `partialWeylElement`,
`partialWeylElement_val`, `partialWeylElement_inv_val`, `partialWeylElement_univ`,
`toIsometryGroup_partialWeylElement`, `toIsometryGroup_weylElement`, `lagrangianFstBasis`,
`lagrangianFstBasis_apply`, `lagrangianFstBasis_repr`, `restrictLagrangianFst`,
`toMatrix_restrictLagrangianFst`, `det_restrictLagrangianFst`, `toIsometryGroup_siegelLevi_mem`,
`toIsometryGroup_siegelLevi`, `toIsometryGroup_siegelUnipotent_mem`,
`exists_toIsometryGroup_siegelUnipotent`, `siegelLevi_one`, `siegelUnipotent_zero`,
`toIsometryGroup_mem_siegelUnipotent_iff`, `toIsometryGroup_mem_siegelLevi_iff`,
`blockIndexEquiv`, `blockMatrix`, `blockMatrix_mul`,
`blockMatrix_one`, `transpose_blockMatrix`, `map_blockMatrix`, `blockMatrix_hyperbolicForm`,
`toBlocks₂₁_blockMatrix`, `toBlocks₂₂_blockMatrix`, `det_toBlocks₂₂_blockMatrix`,
`blockEmbedding`, `blockEmbedding_val`, `blockEmbedding_mem_siegelParabolic`,
`partialWeylElement_eq_blockEmbedding`, `hermitianFormOf`, `hermitianFormOf_apply`,
`mulVecEquiv`, `toIsometryGroupOfForm`, `toIsometryGroupOfForm_apply`,
`toIsometryGroupOfForm_injective`. All in the name space `Langlands.UnitaryGroup`.

## Dependencies

`Langlands.Group.Unitary.Hyperbolic`, `Langlands.Group.Classical.Bruhat` (with
`Langlands.Group.Classical.SiegelParabolic` and `Langlands.LinearAlgebra.EpsilonHermitian.*`).

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), §4.1,
Definition 4.8, p. 98; §4.4.1, p. 114, and (4.8), p. 115.
