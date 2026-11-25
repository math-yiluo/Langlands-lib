# Lagrangians, polarizations and standard bases

**GKT §4.1.3**: **Definition 4.7**, **Definition 4.8** (p. 98); **§4.2.1**: **Lemma 4.9**,
**Lemma 4.10 (b)**, **Lemma 4.11 (d)** (pp. 101–102); **Lemma 4.14** (the Lagrangian part,
pp. 103–104); **Appendix B.2.1**: **Proposition B.9** (uniqueness), **Proposition B.13**
(pp. 612–613).

The module `Langlands.LinearAlgebra.EpsilonHermitian.Lagrangian` treats Lagrangian subspaces of a
non-degenerate `ε`-Hermitian space over a division ring with involution: the isometry group acts
on them as in GKT §4.1–4.2, and every polarization has standard bases. In the book `W` is a right
`−ε`-Hermitian space; here the sign is a parameter and the space is the left space `^τW`
(`Basic.lean`), which changes nothing in this file. Where a statement needs `2` invertible it
assumes `[NeZero (2 : D)]`.

## Content

Let `h : EpsilonHermitianForm τ ε V` be non-degenerate, `V` finite-dimensional.

- `IsLagrangian h X : Prop := h.orthogonal X = X` (the book's Lemma 4.10 (b) taken as the
  definition) and `IsSplit h` (there are Lagrangians `X`, `Y` with `IsCompl X Y`: a complete
  polarization, Definition 4.7). Basic facts: `IsLagrangian.isTotallyIsotropic`,
  `IsLagrangian.two_mul_finrank : 2 * finrank D X = finrank D V`,
  `isLagrangian_of_two_mul_finrank`, `IsLagrangian.map` (the image under an isometry),
  `IsLagrangian.isCompl_iff_disjoint` (two Lagrangians are transverse iff complementary).
- **Definition 4.7 / Lemma 4.10 (b)**: `isLagrangian_iff_maximal` — for a split space, `X` is a
  Lagrangian iff it is a maximal totally isotropic subspace. *Remark:* the book's Lemma 4.10 (b)
  ("an easy exercise") needs `W` split, which chapter 4 assumes throughout: in an anisotropic space
  `0` is maximal totally isotropic and not equal to its orthogonal. The proof here does not use
  Witt's theorem: if `X` is maximal totally isotropic and `X ≠ X^⊥`, a Lagrangian `L` of `V`
  gives the Lagrangian `L_X` of the non-zero non-degenerate space `X^⊥/X` (Lemma 4.14), which is
  non-zero, and a vector of `L ∩ X^⊥` outside `X` enlarges `X`.
- **Lemma 4.11 (d)**: `IsLagrangian.sup_eq_orthogonal_inf : X ⊔ Y = h.orthogonal (X ⊓ h.orthogonal Y)`.
- **Proposition B.13**: `IsSplit.exists_isCompl`.
- `IsLagrangian.exists_isLagrangian_isCompl`: every Lagrangian has a Lagrangian complement (from
  Lemma 4.11 (a)).
- **Lemma 4.14** (Lagrangian part): `reductionSubmodule M X` is the image `X_M` of `X ∩ M^⊥` in
  `M^⊥/M` (`mem_reductionSubmodule`), and `IsLagrangian.reduction`: for `M` totally isotropic and
  `X` a Lagrangian, `X_M` is a Lagrangian of `(M^⊥/M, ⟨,⟩_M)`. The proof computes `X_M^⊥` through
  `(X ∩ M^⊥)^⊥ = X + M`, without the book's dimension count.
- **Lemma 4.9**: `exists_isometry_extend` — for polarizations `V = X ⊕ Y = X' ⊕ Y'` and a linear
  isomorphism `f : X ≃ₗ[D] X'` there is `g : h.isometryGroup` with `g x = f x` on `X` and
  `Y.map g = Y'`; `eq_of_isometry_extend` — such `g` is unique (it is determined by `g|_X` and
  `g Y ≤ Y'`). The construction: `g y ∈ Y'` is the unique vector with `h (f x) (g y) = h x y` for
  all `x ∈ X` (`exists_mem_forall_apply_eq` of `Isotropic.lean`), then `g` is glued on
  `X ⊕ Y` with `LinearMap.ofIsCompl`.
- `exists_isometry_map_eq`: the isometry group acts transitively on Lagrangians (GKT §4.1.3, "the
  Witt extension theorem implies that the action is transitive"; here from Lemma 4.9).
- **Definition 4.8**: `StandardBasis h ι` — a basis `e₁, …, eₙ, e₁*, …, eₙ*` indexed by `ι ⊕ ι`
  (`basis (inl i) = eᵢ`, `basis (inr i) = eᵢ*`) with `h(eᵢ, eⱼ) = h(eᵢ*, eⱼ*) = 0` and
  `h(eᵢ, eⱼ*) = δᵢⱼ`; `apply_inr_inl` (`h(eⱼ*, eᵢ) = ε δᵢⱼ`), `fst`, `snd`, the Lagrangians
  `lagrangianFst = span {eᵢ}` and `lagrangianSnd = span {eᵢ*}`
  (`isLagrangian_lagrangianFst`, `isLagrangian_lagrangianSnd`,
  `isCompl_lagrangianFst_lagrangianSnd`), `nondegenerate` (a standard basis forces
  non-degeneracy), `finrank_eq`, `reindex`, and `isometryEquiv` with `isometryEquiv_apply_basis`:
  two spaces with standard bases indexed by the same type are isometric through the bases (for one
  index: the uniqueness of the hyperbolic plane, **Proposition B.9**).
- `exists_standardBasis`: for a polarization `V = X ⊕ Y` and a basis `b` of `X` there is a standard
  basis with `eᵢ = bᵢ`, `span {eᵢ} = X`, `span {eᵢ*} = Y`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025):
  §4.1.3, Definitions 4.7 and 4.8, p. 98; §4.2.1, Lemmas 4.9, 4.10, 4.11, pp. 101–102;
  Lemma 4.14, pp. 103–104; Appendix B.2, Proposition B.9, p. 612; Proposition B.13, p. 613.

## Declarations

In `Langlands.EpsilonHermitianForm`: `IsLagrangian`, `IsSplit`,
`IsLagrangian.isTotallyIsotropic`, `IsLagrangian.mem_orthogonal_iff`, `IsLagrangian.apply_eq_zero`,
`IsLagrangian.two_mul_finrank`, `isLagrangian_of_two_mul_finrank`, `IsLagrangian.map`,
`IsLagrangian.isCompl_iff_disjoint`, `IsLagrangian.sup_eq_orthogonal_inf`,
`IsSplit.exists_isCompl`, `IsLagrangian.exists_isLagrangian_isCompl`, `reductionSubmodule`,
`mem_reductionSubmodule`, `IsLagrangian.reduction`, `isLagrangian_iff_maximal`,
`exists_isometry_extend`, `eq_of_isometry_extend`, `exists_isometry_map_eq`, `StandardBasis`
(fields `basis`, `apply_inl_inl`, `apply_inr_inr`, `apply_inl_inr`), `StandardBasis.fst`,
`StandardBasis.snd`, `StandardBasis.apply_inr_inl`, `StandardBasis.lagrangianFst`,
`StandardBasis.lagrangianSnd`, `StandardBasis.nondegenerate`,
`StandardBasis.fst_mem_lagrangianFst`, `StandardBasis.snd_mem_lagrangianSnd`,
`StandardBasis.isTotallyIsotropic_lagrangianFst`, `StandardBasis.isTotallyIsotropic_lagrangianSnd`,
`StandardBasis.finrank_lagrangianFst`, `StandardBasis.finrank_lagrangianSnd`,
`StandardBasis.finrank_eq`, `StandardBasis.isLagrangian_lagrangianFst`,
`StandardBasis.isLagrangian_lagrangianSnd`, `StandardBasis.isCompl_lagrangianFst_lagrangianSnd`,
`StandardBasis.isometryEquiv`, `StandardBasis.isometryEquiv_apply_basis`, `StandardBasis.reindex`,
`exists_standardBasis`.

Private: `exists_rep` (the vector `g y` of Lemma 4.9).

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.Isotropic`.
- Mathlib: `LinearAlgebra.Projection`.
