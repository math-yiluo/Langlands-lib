/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.Defs
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

set_option linter.privateModule false

/-! # Section maps that are isomorphisms on all geometric stalks

Source: Stacks Project, Tags 03PT and 0GKC, stalkwise-isomorphism step.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w v u' v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

private noncomputable def restrictionStalkIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [LocallySmall.{w} C] (Φ : J.Point.{w}) {U : C} (a : Φ.fiber.obj U)
    {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
    (G : Sheaf J A) : (Φ.over a).sheafFiber.obj (G.over U) ≅ Φ.sheafFiber.obj G := by
  let e := FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber a
  let F := e.functor ⋙ Over.forget (Φ.fiber.elementsMk U a)
  have : F.Initial := inferInstance
  change colimit ((Functor.Elements.π (Φ.over a).fiber).op ⋙ (G.over U).obj) ≅
    colimit ((Functor.Elements.π Φ.fiber).op ⋙ G.obj)
  change colimit (F.op ⋙ (Functor.Elements.π Φ.fiber).op ⋙ G.obj) ≅ _
  exact Functor.Final.colimitIso F.op _

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
