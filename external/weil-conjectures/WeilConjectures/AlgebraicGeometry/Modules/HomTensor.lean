/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Free
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Presheaf

/-!
# `Hom(M, N) ≅ Mᵛ ⊗ N` for an invertible `N`

This module only re-exports its parts, which live in
`WeilConjectures.AlgebraicGeometry.Modules.HomTensor`; it was split to keep the compilation of
each part cheap.

For sheaves of modules `M`, `N` on a scheme there is a natural morphism
`Mᵛ ⊗ N ⟶ Hom(M, N)`, `φ ⊗ n ↦ (m ↦ φ(m) n)`. If `N` is invertible it is an isomorphism: it is
the sheafification of a morphism of presheaves of modules which is bijective on sections over
every open on which `N` is trivial.

## Main definitions and results

- `PresheafOfModules.dualTensorHom`: the morphism `Hom(M, R) ⊗ P ⟶ Hom(M, P)` of presheaves of
  modules, and `PresheafOfModules.dualTensorHom_app_bijective`: it is bijective on sections
  over an object on which `P` is free of rank one.
- `AlgebraicGeometry.Scheme.Modules.dualTensorHom`: the morphism `Mᵛ ⊗ N ⟶ Hom(M, N)` of sheaves
  of modules on a scheme.
- `AlgebraicGeometry.Scheme.Modules.isIso_dualTensorHom`: it is an isomorphism if `N` is
  invertible.
- `AlgebraicGeometry.Scheme.Modules.isIso_dualTensorHom_of_isFiniteLocallyFree`: it is an
  isomorphism if `M` is finite locally free.
- `AlgebraicGeometry.Scheme.Modules.dualTensorHom_naturality_right`: it is natural in `N`.
- `AlgebraicGeometry.Scheme.Modules.dualTensorHomIso`: the natural isomorphism
  `Mᵛ ⊗ N ≅ Hom(M, N)` for an invertible `N`.
-/
