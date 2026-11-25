/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # A concrete pullback for extending an open submodule

Source: Stacks Project, Properties, Lemma 01PF, binary gluing step.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction/direct-image adjunction for V inside the union. -/
noncomputable def binarySubmoduleAdjunction (X : Scheme.{u}) (W V : X.Opens) :=
  SheafOfModules.overMapPushforwardAdj (moduleRings X.toRingedSpace)
    (homOfLE (show V ≤ W ⊔ V from le_sup_right))

/-- Transitivity of restriction from X through the union to V. -/
noncomputable def binarySubmoduleRestrictionIso (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
    (homOfLE (show V ≤ W ⊔ V from le_sup_right))).app H

/-- Direct image of the inclusion, transported to the iterated restriction. -/
noncomputable def binarySubmoduleMap (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V) :=
  (SheafOfModules.overPullback (moduleRings X.toRingedSpace)
      (homOfLE (show V ≤ W ⊔ V from le_sup_right))).map
    (ι ≫ (binarySubmoduleRestrictionIso X W V H).inv)

/-- Pull back the direct image of Q along the restriction unit of H on the union.
This constructs the submodule without choosing any witness of an existence theorem.
Source: Stacks Project, Properties, Lemma 01PF, binary gluing step.
(blueprint: def-weil-pbc-module-binary-submodule-pullback) -/
noncomputable def binarySubmodule (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V) :=
  CategoryTheory.Limits.pullback ((binarySubmoduleAdjunction X W V).unit.app (H.over (W ⊔ V)))
    (binarySubmoduleMap X W V H Q ι)

/-- The first pullback projection to the ambient module on the union. -/
noncomputable def binarySubmoduleInclusion (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V) :=
  pullback.fst ((binarySubmoduleAdjunction X W V).unit.app (H.over (W ⊔ V)))
    (binarySubmoduleMap X W V H Q ι)

/-- The pullback inclusion is monic: direct image, a right adjoint, preserves the
monomorphism Q to H on V, and pullback preserves monomorphisms.
Source: Stacks Project, Properties, Lemma 01PF, submodule gluing.
(blueprint: lem-weil-pbc-module-binary-submodule-mono) -/
instance binarySubmoduleInclusion_mono (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V) [Mono ι] :
    Mono (binarySubmoduleInclusion X W V H Q ι) := by
  have : (SheafOfModules.overPullback (moduleRings X.toRingedSpace)
      (homOfLE (show V ≤ W ⊔ V from le_sup_right))).IsRightAdjoint :=
    (binarySubmoduleAdjunction X W V).isRightAdjoint
  have : Mono (binarySubmoduleMap X W V H Q ι) := by
    exact Functor.map_mono
      (SheafOfModules.overPullback (moduleRings X.toRingedSpace)
        (homOfLE (show V ≤ W ⊔ V from le_sup_right)))
      (ι ≫ (binarySubmoduleRestrictionIso X W V H).inv)
  exact inferInstanceAs (Mono (pullback.fst _ _))

end AlgebraicGeometry.Scheme.Modules
