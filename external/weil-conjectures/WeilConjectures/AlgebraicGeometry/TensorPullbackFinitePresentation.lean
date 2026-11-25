/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Tensor pullback preserves finite presentation

Source: Stacks Project, Tag 01BQ, and tensor pullback, Tags 0095--0097.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling back a finitely presented scheme module preserves finite presentation.
Source: Stacks Project, modules.tex, Tag 01BQ; sheaves.tex, Tags 0095--0097.
(blueprint: lem-pc-tensor-pullback-finite-presentation).

Proof: choose the local finite free presentations expressing finite presentation of M.
The inverse images of their open domains cover X. Restriction of tensor pullback to
one such inverse-image open is pullback of the corresponding restricted module.
Inverse image and sheafified extension of scalars are left adjoints, so their composite
preserves the cokernel presentation. Pullback of the structure module is the structure
module by the multiplication isomorphism b tensor a maps to b g-sharp(a), inverse
b maps to b tensor 1. It therefore preserves the finite free modules in both degrees
of each presentation, with their original finite index sets. These presentations on
the inverse-image cover give QuasicoherentData with finite presentations, exactly
SheafOfModules.IsFinitePresentation. Empty inverse-image opens may be discarded;
an empty source has the empty cover. No flatness hypothesis on g is required. -/
theorem isFinitePresentation_tensorPullback
    {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((tensorPullback g).obj M).IsFinitePresentation := by
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g
  let e := adj.leftAdjointUniq (pullbackPushforwardAdjunction g)
  exact isFinitePresentation_of_iso (e.app M).symm

end AlgebraicGeometry.Scheme.Modules
