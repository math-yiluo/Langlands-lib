/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherent modules on a scheme

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.isCoherent`: coherent `𝒪_X`-modules, as a property of objects.

## Implementation notes

Mathlib has no `IsCoherent` class for sheaves of modules; as elsewhere in the project, coherence
is spelled as quasi-coherence together with finite presentation.

This agrees with coherence in the sense of Stacks `01BV` (finite type, and every finite type
submodule over an open is of finite presentation) only on locally noetherian schemes
(Stacks `01XZ`). On a general scheme it is weaker: `𝒪_X` is always quasi-coherent of finite
presentation, but it is coherent only if `X` is locally coherent, which fails for instance for
`Spec k[x₁, x₂, …]/(x₁x₂, x₁x₃, …)`. Results about `isCoherent` that need the Stacks notion
must therefore assume `X` locally noetherian.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) in
/-- The coherent `𝒪_X`-modules, i.e. the quasi-coherent `𝒪_X`-modules of finite presentation, as
a property of objects of `X.Modules`. -/
abbrev Scheme.Modules.isCoherent : ObjectProperty X.Modules :=
  fun ℱ ↦ SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ ∧
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ

end AlgebraicGeometry
