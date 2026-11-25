/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-!
# Cohomology of quasi-coherent sheaves on affine schemes

This module only re-exports its parts, which live in
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine`; it was split to keep the compilation of
each part cheap.

Serre's vanishing theorem says that the higher cohomology of a quasi-coherent sheaf of modules
on an affine scheme vanishes. Its standard consequence is Leray's theorem: the Čech cohomology
of an open covering all of whose finite intersections are affine computes the sheaf cohomology
of any quasi-coherent sheaf of modules. This applies to every open affine covering of a scheme
which is separated over an affine base.

The Čech complex of a family of open subsets `U : ι → X.Opens` with coefficients in a presheaf
is `CategoryTheory.cechComplexFunctor`: the finite products used there are the finite
intersections `U i₀ ⊓ ⋯ ⊓ U iₙ`, so its `q`-th cohomology is the Čech cohomology `Ȟ^q(𝔘, ℱ)`
of the covering. We take the coefficients in `ℱ.presheafModuleCat`, the presheaf of
`Γ(X, ⊤)`-modules underlying `ℱ`, so that `Ȟ^q(𝔘, ℱ)` is a `Γ(X, ⊤)`-module.

## Implementation notes

The blueprint states Leray's theorem as "the edge map of the Čech-to-derived spectral sequence
is an isomorphism". The edge map is not available as a definition, so
`nonempty_cechComplex_linearEquiv_H` only records the existence of a `Γ(X, ⊤)`-linear
isomorphism, without identifying it with the edge map. For `X` over a base `S`, linearity over
`Γ(X, ⊤)` gives linearity over `Γ(S, 𝒪_S)` acting through `X ⟶ S`, and over `k` when
`S = Spec k`, which is what the tangent-space computation of the Jacobian needs. Identifying
the isomorphism awaits the edge map of `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`: the higher cohomology of a
  quasi-coherent sheaf of modules on an affine scheme vanishes.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H`: Leray's theorem, i.e.
  Čech cohomology of an open covering with affine finite intersections computes the cohomology
  of a quasi-coherent sheaf, linearly over the global functions.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated`: the
  case of an open affine covering of a scheme separated over an affine base.
- `AlgebraicGeometry.Scheme.Modules.finrankH_pushforward_of_isAffineHom`: the pushforward along
  an affine morphism preserves the cohomology of quasi-coherent sheaves of modules.
-/
