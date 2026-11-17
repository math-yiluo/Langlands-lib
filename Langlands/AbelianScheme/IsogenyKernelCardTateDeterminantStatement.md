# The `p`-adic size of the kernel of an isogeny

`Langlands.AbelianScheme.IsogenyKernelCardTateDeterminantStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. For every algebraically closed field `k : Type u`, every abelian scheme `A` over `Spec k`, every prime `p` with `(p : k) ≠ 0` and every isogeny `α : A ⟶ A`, the `p`-adic norm of the number of `k`-points of the kernel of `α`,

`‖((Nat.card (GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))).ker : ℕ) : ℚ_[p])‖`,

equals the `p`-adic norm `‖LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α)‖` of the determinant of the actual rational `p`-adic Tate map of `α`.

`GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))` is the existing homomorphism that `α` induces on `k`-points (module `Langlands/AbelianScheme/AlgClosedIsogenyPoints.lean`). Its kernel is finite by `IsIsogeny.finite_ker_pointsHom`. `Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α` is the `ℚ_[p]`-linear map that `α` induces on the rational `p`-adic Tate module of the `k`-points of `A`.

## Source

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers.

- p. 23, proof of Proposition 12.9: for `β ∈ End(A)`, `k` separably closed and `l ≠ char(k)`,
  `|#Ker(β)|_l = (#Ker(β)(l))^{-1} = (#Coker(T_l β))^{-1} = |det(T_l β)|_l`,
  where `Ker(β)(l)` is the `l`-primary part of the kernel.

The proposition is the equality of the outer terms of this chain for an isogeny, with `#Ker(β)` read as the number of `k`-points of the kernel and `T_l β` replaced by its rational extension, which has the same determinant. The number of `k`-points is used rather than the order of the kernel group scheme. In positive characteristic the two differ only by a power of the characteristic, which has `p`-adic norm `1`.

## Scope

The field is algebraically closed and of any characteristic; the prime is any prime invertible in `k`. This is one of the four inputs of `IsogenyDegreeTateDeterminantNormReductionStatement` (Task 7330).
