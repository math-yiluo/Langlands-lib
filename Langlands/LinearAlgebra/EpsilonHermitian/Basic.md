# `ε`-Hermitian forms over a division ring with involution

**GKT Appendix B.2.1**: **Definition B.4**, **Proposition B.6**, **Definition B.7**, **Proposition
B.16** (pp. 611–614); **§4.2.1**: the orthogonal complement and **Lemma 4.11 (b), (c)**
(pp. 101–102); **§4.3.1**: **Lemma 4.18** (p. 107).

The module `Langlands.LinearAlgebra.EpsilonHermitian.Basic` defines `ε`-Hermitian forms on left
modules over a division ring with involution, their isometry groups and isometries, orthogonal
complements with their dimension, and non-degenerate subspaces. Nothing here needs `2` to be
invertible.

## Conventions and the dictionary with the book

- `D` is a `DivisionRing` and `τ : RingInvo D` a ring involution in Mathlib's sense
  (`D ≃+* Dᵐᵒᵖ` of order two); `RingInvo.conj τ d = (τ d).unop` is the book's `d^τ`. For a field
  with the trivial involution (GKT Case 1) take `RingInvo.id F`; for a commutative ring `R` with an
  involutive ring endomorphism `c`, `RingInvo.ofInvolutive c hc : RingInvo R` is `c`
  (`conj_ofInvolutive`). `ε : ℤˣ`, read in `D` as
  `((ε : ℤ) : D)`.
- `EpsilonHermitianForm τ ε V` on a left `D`-module `V` is the book's left `ε`-Hermitian form of
  Definition B.4: `h (a • x) y = a * h x y` and `h y x = ε (h x y)^τ`, hence
  `h x (a • y) = h x y * a^τ`. Non-degeneracy, which the book puts into Definition B.4, is the
  separate predicate `Nondegenerate`, so that restrictions to subspaces are forms of the same kind.
- The book's chapter 4 works with a *right* `−ε`-Hermitian space `W`. By Proposition B.6 it is the
  left space `^τW` (`d · w = w d^τ`) with the same form values; `TwistedRight τ W` and `ofRight`
  realize this for a module `W` over `Dᵐᵒᵖ`. Subspaces, isometries, Lagrangians and the Leray
  invariant do not depend on the side; only determinants do (see the page of
  `Langlands/Theta/Metaplectic/RaoFunction.lean`).
- Relation to existing notions. For `D = F` a field and `τ = id`, a bilinear form `B` with
  `B y x = ε B x y` is `ofBilinForm B hB`, and its isometry group is the group
  `LinearMap.BilinForm.isometryGroup B` of `Langlands/LinearAlgebra/Symplectic.lean` by
  definition (`isometryGroup_ofBilinForm`, proved by `rfl`); for `ε = -1` it is `Sp(W)`.
  Mathlib's sesquilinear forms `M →ₛₗ[I] M →ₗ[R] R` exist only over commutative rings, which is
  why the notion is new. The Library's matrix notions (`UnitaryGroup.ofForm c J` with
  `Matrix.IsHermitianFor` in `Langlands/Group/Unitary/Basic.lean`, `FirstKindInvolution.sesqForm`
  in `Langlands/GroupScheme/Quaternionic/Forms.lean`) are Gram matrices of such forms on row vectors
  in the left convention used here; they are not restated.

## Content

Let `h : EpsilonHermitianForm τ ε V`.

- **Basic identities**: `map_add_left`, `map_add_right`, `map_smul_left`, `map_smul_right`,
  `map_zero_left/right`, `map_neg_left/right`, `map_sub_left/right`, `map_sum_left/right`,
  `conj_swap : h y x = ε * conj τ (h x y)`, `conj_apply`, `conj_apply_self`
  (`h(x,x)^τ = ε h(x,x)`), `apply_eq_zero_comm` (`h x y = 0 ↔ h y x = 0`), and the linear form
  `flipApply y : V →ₗ[D] D`, `v ↦ h v y`. The involution: `RingInvo.conj_conj`, `conj_mul`
  (`(ab)^τ = b^τ a^τ`), `conj_add`, `conj_inv`, `conj_intCast`, `conj_two`, `conj_sum`.
- **New forms from old**: `restrict U : EpsilonHermitianForm τ ε U`, `comp f`, `-h`, and
  `smul a ha hτ` (`a h` for `a` central and `τ`-fixed; GKT 4.3.4, 4.5.7). `ext_basis`: two forms
  agreeing on all pairs of basis vectors are equal.
- **Orthogonal complement** (GKT §4.2.1): `orthogonal U = {v | ∀ u ∈ U, h v u = 0}`
  (`mem_orthogonal`, `mem_orthogonal'`); it is antitone, `U ≤ U^⊥⊥`, `(U ⊔ U')^⊥ = U^⊥ ⊓ U'^⊥`,
  `(⨆ Uᵢ)^⊥ = ⨅ Uᵢ^⊥`, `⊥^⊥ = ⊤`.
- **Non-degeneracy** `Nondegenerate h : Prop := ∀ x, (∀ y, h x y = 0) → x = 0`, with
  `eq_zero_of_right`, `ext_left`, `ext_right`; `orthogonal_top`.
- **Dimension** (finite-dimensional `V`, non-degenerate `h`):
  `finrank_add_finrank_orthogonal : finrank D U + finrank D (h.orthogonal U) = finrank D V` for
  every `U` (GKT Lemma 4.11 (c), stated there for isotropic `U`);
  `orthogonal_orthogonal : h.orthogonal (h.orthogonal U) = U` (Lemma 4.11 (b));
  `orthogonal_inf`, `orthogonal_injective`, `orthogonal_le_orthogonal_iff`,
  `orthogonal_eq_bot_iff`.
- **Non-degenerate subspaces** (GKT Lemma 4.18): `restrict_nondegenerate_iff`
  (`(h.restrict U).Nondegenerate ↔ U ⊓ U^⊥ = ⊥`), `isCompl_orthogonal_of_restrict_nondegenerate`
  (`IsCompl U U^⊥`), `restrict_orthogonal_nondegenerate`.
- **Isometry group** (GKT B.2.3, §4.1.3): `isometryGroup h : Subgroup (V ≃ₗ[D] V)`, the `g` with
  `h (g x) (g y) = h x y`; `mem_isometryGroup_iff`, `isometryGroup_apply`, the coercion lemmas,
  `mem_isometryGroup_of_basis` (preserving the form on a basis suffices), `map_orthogonal`
  (`g(U^⊥) = (gU)^⊥`), `injective_of_map_apply` and `ofLinearMap` (a form-preserving linear
  endomorphism of a non-degenerate finite-dimensional space is an isometry).
- **Proposition B.16**: `map_smul_of_map_apply` — an additive bijection preserving a non-degenerate
  form is `D`-linear.
- **Isometries between spaces** (Definition B.7): `IsometryEquiv h h'` (a linear equivalence
  preserving the forms), with `refl`, `symm`, `trans`, `map_app`.
- **Bilinear case**: `ofBilinForm`, `isometryGroup_ofBilinForm`.
- **Proposition B.6**: `TwistedRight τ W` (a type synonym of a `Dᵐᵒᵖ`-module `W`, a left
  `D`-module by `d • w = w d^τ`, `TwistedRight.smul_def`) and `ofRight f …` (a right
  `ε`-Hermitian form, `f (w d) w' = d^τ f w w'`, is a left `ε`-Hermitian form on `^τW`).

**Proof of the dimension formula.** For a basis `b₁, …, bₘ` of `U`, the linear map
`V → D^m`, `v ↦ (h v bᵢ)ᵢ`, has kernel `U^⊥`; it is onto: otherwise a non-zero linear form
`y ↦ ∑ yᵢ cᵢ` on `D^m` kills its image, so `h v (∑ cᵢ^τ bᵢ) = 0` for all `v`, and non-degeneracy
gives `cᵢ = 0`. Rank–nullity (Mathlib, valid over division rings) then gives the formula, and
`U^⊥⊥ = U` follows from `U ≤ U^⊥⊥` and equal dimensions. This avoids dual spaces over a
non-commutative `D`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025):
  §4.1.1 and §4.1.3, pp. 93–97; §4.2.1, Lemma 4.11, pp. 101–102; Lemma 4.18, p. 107;
  Appendix B.2, Definition B.4, Proposition B.6, Definition B.7, p. 611; B.2.3, Proposition B.16,
  p. 614.

## Declarations

- `Langlands.RingInvo.conj`, `RingInvo.conj_conj`, `conj_add`, `conj_mul`, `conj_zero`,
  `conj_one`, `conj_neg`, `conj_sub`, `conj_intCast`, `conj_natCast`, `conj_ofNat`, `conj_two`,
  `conj_injective`, `conj_surjective`, `conj_eq_zero_iff`, `conj_sum`, `conj_id_apply`,
  `conj_inv`, `ofInvolutive`, `conj_ofInvolutive`; `Langlands.units_int_cast_mul_self'`,
  `units_int_cast_commute`.
- `Langlands.EpsilonHermitianForm` (structure: `toFun`, `map_add_left'`, `map_smul_left'`,
  `conj_swap'`) and, in its name space: `toFun_eq_coe`, `ext`, `map_add_left`, `map_smul_left`,
  `conj_swap`, `conj_apply`, `map_add_right`, `map_smul_right`, `map_zero_left`,
  `map_zero_right`, `map_neg_left`, `map_neg_right`, `map_sub_left`, `map_sub_right`,
  `map_sum_left`, `map_sum_right`, `apply_eq_zero_comm`, `conj_apply_self`, `flipApply`,
  `flipApply_apply`, `restrict`, `restrict_apply`, `comp`, `comp_apply`, `neg_apply`, `smul`,
  `smul_apply`, `Nondegenerate`, `Nondegenerate.eq_zero_of_right`, `Nondegenerate.ext_left`,
  `Nondegenerate.ext_right`, `orthogonal`, `mem_orthogonal`, `mem_orthogonal'`,
  `orthogonal_le_orthogonal`, `le_orthogonal_orthogonal`, `le_orthogonal_iff`, `orthogonal_bot`,
  `orthogonal_top`, `orthogonal_sup`, `mem_orthogonal_span_singleton`, `orthogonal_iSup`,
  `finrank_add_finrank_orthogonal`, `orthogonal_orthogonal`, `orthogonal_le_orthogonal_iff`,
  `orthogonal_injective`, `orthogonal_inf`, `orthogonal_eq_bot_iff`,
  `restrict_nondegenerate_iff`, `isCompl_orthogonal_of_restrict_nondegenerate`,
  `restrict_orthogonal_nondegenerate`, `isometryGroup`, `mem_isometryGroup_iff`,
  `isometryGroup_apply`, `isometryGroup_coe_mul_apply`, `isometryGroup_coe_one_apply`,
  `isometryGroup_coe_inv_apply`, `isometryGroup_coe_inv_apply'`, `ext_basis`,
  `mem_isometryGroup_of_basis`, `map_orthogonal`, `injective_of_map_apply`, `ofLinearMap`,
  `ofLinearMap_apply`, `map_smul_of_map_apply`, `IsometryEquiv` (with `coe_toLinearEquiv`,
  `map_app`, `refl`, `symm`, `trans`, `refl_apply`, `symm_apply_apply`, `apply_symm_apply`,
  `trans_apply`), `ofBilinForm`, `ofBilinForm_apply`, `isometryGroup_ofBilinForm`.
- `Langlands.TwistedRight`, `TwistedRight.mk`, `TwistedRight.get`, `TwistedRight.smul_def`,
  `Langlands.EpsilonHermitianForm.ofRight`.

Private: `coordMap`, `coordMap_apply`, `ker_coordMap`, `coordMap_surjective` (the proof of the
dimension formula).

## Dependencies

- `Langlands.LinearAlgebra.Symplectic` (for `isometryGroup_ofBilinForm`).
- Mathlib: `LinearAlgebra.FiniteDimensional.Lemmas`, `RingTheory.RingInvo`.
