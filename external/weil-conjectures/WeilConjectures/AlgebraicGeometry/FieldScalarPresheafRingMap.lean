/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf

/-! # Scalar extension of module-valued sheaves

Source: Stacks Project, Modules, tensor pullback and its adjunction, Tags 0095 and 0096.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

variable {k : Type u} [Ring k] (X : TopCat.{u})
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (α : k →+* R.obj.obj (op ⊤))

/-- The structural map from the constant presheaf of rings.
(blueprint: def-sc-field-scalar-presheaf-ring-map). -/
noncomputable def fieldScalarPresheafRingMap :
    (Functor.const (Opens X)ᵒᵖ).obj (RingCat.of k) ⟶ (𝟭 (Opens X)).op ⋙ R.obj where
  app U := RingCat.ofHom ((R.obj.map (isTerminalTop.op.to U)).hom.comp α)
  naturality U V f := by
    ext a
    change R.obj.map (isTerminalTop.op.to V) (α a) =
      R.obj.map f (R.obj.map (isTerminalTop.op.to U) (α a))
    rw [← RingCat.comp_apply, ← R.obj.map_comp]
    congr 2

/-- Regard a module-valued presheaf as modules over the constant ring presheaf.
(blueprint: def-sc-module-presheaf-constant-modules). -/
noncomputable def modulePresheafToConstantModules :
    ((Opens X)ᵒᵖ ⥤ ModuleCat.{max u v} k) ⥤
      PresheafOfModules.{max u v} ((Functor.const (Opens X)ᵒᵖ).obj (RingCat.of k)) where
  obj V :=
    { obj := V.obj
      map := fun f ↦ ModuleCat.ofHom (V.map f).hom
      map_id := fun U ↦ by ext a; exact ConcreteCategory.congr_hom (V.map_id U) a
      map_comp := fun f g ↦ by ext a; exact ConcreteCategory.congr_hom (V.map_comp f g) a }
  map f :=
    { app := f.app
      naturality := fun g ↦ by ext a; exact ConcreteCategory.congr_hom (f.naturality g) a }

end SheafOfModules
