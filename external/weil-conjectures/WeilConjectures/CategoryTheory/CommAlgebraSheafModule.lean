/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Sheaf

/-! # Underlying modules of commutative algebra sheaves

Source: Stacks Project, Sheaves, Section 009E and Lemma 0087; Modules, Lemma 01AH
(blueprint: proposition-proper-direct-image-constructible-complexes).
-/

@[expose] public section

universe uA

open CategoryTheory TopologicalSpace

namespace CategoryTheory

variable {X : Type uA} [TopologicalSpace X]

local notation "J" => Opens.grothendieckTopology X

/-- The underlying module of an algebra sheaf is its unit module restricted along the
structure map. Source: Stacks Project, Modules, Lemma 01AH and Sheaves, Lemma 0087
(blueprint: proposition-proper-direct-image-constructible-complexes). -/
noncomputable def commAlgebraSheafModule (O : Sheaf J CommRingCat.{uA})
    (A : Under O) :
    SheafOfModules.{uA} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map A.hom)).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A.right))

set_option backward.isDefEq.respectTransparency false in
/-- Algebra-sheaf morphisms act on the underlying modules by the same section maps.
Source: Stacks Project, Modules, Lemma 01AH and Sheaves, Lemma 0087
(blueprint: proposition-proper-direct-image-constructible-complexes). -/
noncomputable def commAlgebraSheafModuleFunctor (O : Sheaf J CommRingCat.{uA}) :
    Under O ⥤
      SheafOfModules.{uA} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) where
  obj := commAlgebraSheafModule O
  map := fun {A B} f ↦
    { val := PresheafOfModules.homMk
        (Functor.whiskerRight f.right.hom
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
          intro U r a
          change A.right.obj.obj U at a
          change O.obj.obj U at r
          change (f.right.hom.app U).hom ((A.hom.hom.app U).hom r * a) =
            (B.hom.hom.app U).hom r * (f.right.hom.app U).hom a
          rw [map_mul]
          congr 1
          exact congrArg (fun t ↦ t.hom.app U r) (Under.w f)
        ) }

end CategoryTheory
