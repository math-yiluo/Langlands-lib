# The degree of an isogeny in characteristic zero counts its kernel points

`Langlands.AbelianScheme.IsogenyFinrankKernelCardStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. For every algebraically closed field `k : Type u` of characteristic zero, all abelian schemes `A` and `B` over `Spec k`, every isogeny `α : A ⟶ B` (`IsIsogeny α`: finite, flat and surjective) and every point `y` of the scheme `B.X.left`, the rank `(hom α).finrank y` of the finite flat underlying morphism equals

`Nat.card (GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))).ker`.

Here `GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))` is the existing homomorphism (module `Langlands/AbelianScheme/AlgClosedIsogenyPoints.lean`) that `α` induces on the groups of `k`-points `Over.mk (𝟙 _) ⟶ A.X` and `Over.mk (𝟙 _) ⟶ B.X`. Its kernel is the group of `k`-points of the kernel of `α`. It is finite by the published `IsIsogeny.finite_ker_pointsHom`. `Scheme.Hom.finrank` is Mathlib's rank of a morphism at a point of its target.

## Source

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers.

- p. 12, Section 8. When `k` has characteristic zero, the kernel `N` of a homomorphism of abelian varieties is reduced (Milne cites Shatz). The degree of an isogeny `f` is the order of the finite group scheme `Ker(f)`, equivalently the rank of `f_* 𝒪_A` as a locally free `𝒪_B`-module.

A reduced finite group scheme over an algebraically closed field has as many `k`-points as its order. So in characteristic zero the rank of `f_* 𝒪_A` is the number of `k`-points of the kernel. The proposition states this equality, with the rank taken at every point of `B`.

## Scope

The characteristic-zero hypothesis is needed: in characteristic `p > 0` an inseparable isogeny has a non-reduced kernel, and the equality fails. This is one of the four inputs of `IsogenyDegreeTateDeterminantNormReductionStatement` (module `Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormReduction`).
