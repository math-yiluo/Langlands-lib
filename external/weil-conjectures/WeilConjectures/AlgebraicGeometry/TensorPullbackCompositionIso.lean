/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Canonical comparison for successive tensor pullbacks

Source: Stacks Project, Sheaves of Modules, Tags 0095 and 0096.
(blueprint: def-pc-tensor-pullback-composition-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical composition comparison, via the adjunctions to pushforward.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: def-pc-tensor-pullback-composition-iso). -/
noncomputable def tensorPullbackCompositionIso
    {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (h : Y ⟶ X) (k : Z ⟶ X) (w : g ≫ h = k) :
    tensorPullback k ≅ tensorPullback h ⋙ tensorPullback g :=
  (conjugateIsoEquiv
    ((Classical.choose (exists_tensorPullbackAdjunction h)).comp
      (Classical.choose (exists_tensorPullbackAdjunction g)))
    (Classical.choose (exists_tensorPullbackAdjunction k))).symm
    (pushforwardComp g h ≪≫ pushforwardCongr w)

end AlgebraicGeometry.Scheme.Modules
