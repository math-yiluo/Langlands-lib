/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Presheaf

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Common representatives in topological ring and abelian pullbacks

Source: Stacks Project, Sheaves, Tag 008T; Categories, Tag 002W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace PresheafOfModules

/-- A ring section and an abelian section of topological pullbacks admit
representatives on a single neighbourhood. Source: Stacks Project, Sheaves, Tag 008T.
Proof: The costructured-arrow diagram at U is nonempty, since it contains the top
open, and filtered, since intersection gives a common later open. The forgetful
functors from commutative rings and abelian groups preserve its colimit. Thus each
section has a representative. Intersect their two neighbourhoods and restrict the
two representatives; the cocone identity preserves their images. This also works
for empty opens and zero rings or groups.
(blueprint: lem-pc-topological-pullback-common-representatives) -/
theorem topologicalPullbackCommonRepresentatives {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : Y.Presheaf CommRingCat.{u}) (A : Y.Presheaf Ab.{u}) (U : Opens X)
    (x : ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj O).obj (op U))
    (y : ((TopCat.Presheaf.pullback Ab.{u} f).obj A).obj (op U)) :
    let ι := fun (C : Type (u + 1)) [Category.{u} C] [HasColimits C]
      (A : Y.Presheaf C) (U : Opens X) (V : Opens Y)
      (h : U ≤ (Opens.map f).obj V) =>
        ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app A).app (op V) ≫
          ((TopCat.Presheaf.pullback C f).obj A).map (homOfLE h).op
    ∃ (V : Opens Y) (h : U ≤ (Opens.map f).obj V)
        (a : O.obj (op V)) (g : A.obj (op V)),
      (ι CommRingCat.{u} O U V h).hom a = x ∧
        (ι Ab.{u} A U V h).hom g = y := by
  dsimp only
  let L := (Opens.map f).op
  let J := CostructuredArrow L (op U)
  have : IsFiltered J :=
    { nonempty := ⟨CostructuredArrow.mk (homOfLE (show U ≤
          (Opens.map f).obj ⊤ from le_top)).op⟩
      cocone_objs := fun j k => by
        have h : U ≤ (Opens.map f).obj (j.left.unop ⊓ k.left.unop) := by
          intro z hz
          exact ⟨j.hom.unop.le hz, k.hom.unop.le hz⟩
        let m : J := CostructuredArrow.mk (homOfLE h).op
        exact ⟨m, CostructuredArrow.homMk (homOfLE inf_le_left).op (by subsingleton),
          CostructuredArrow.homMk (homOfLE inf_le_right).op (by subsingleton), trivial⟩
      cocone_maps := fun j k v w => ⟨k, 𝟙 k, by ext; subsingleton⟩ }
  let cO := (Functor.LeftExtension.mk _ (L.leftKanExtensionUnit O)).coconeAt (op U)
  let cA := (Functor.LeftExtension.mk _ (L.leftKanExtensionUnit A)).coconeAt (op U)
  obtain ⟨j, a, ha⟩ := Concrete.isColimit_exists_rep _
    (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit O (op U)) x
  obtain ⟨k, g, hg⟩ := Concrete.isColimit_exists_rep _
    (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit A (op U)) y
  let m := IsFiltered.max j k
  let v := IsFiltered.leftToMax j k
  let w := IsFiltered.rightToMax j k
  refine ⟨m.left.unop, m.hom.unop.le, O.map v.left a, A.map w.left g, ?_, ?_⟩
  · change (cO.ι.app m).hom (O.map v.left a) = x
    rw [← ha]
    exact ConcreteCategory.congr_hom (cO.w v) a
  · change (cA.ι.app m).hom (A.map w.left g) = y
    rw [← hg]
    exact ConcreteCategory.congr_hom (cA.w w) g

end PresheafOfModules
