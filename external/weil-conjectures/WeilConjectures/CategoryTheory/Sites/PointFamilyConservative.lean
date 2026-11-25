/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Conservative families of points

Source: Stacks Project, Sites, Tags 00YK and 00YM, using Tags 00Y6 and 00Y8
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

namespace CategoryTheory

open Limits Opposite

/-- The sheaf morphism represented by a section of a sheaf on an object.
Source: Stacks, Tags 00Y6 and 00Y8 (auxiliary; not a blueprint node). -/
noncomputable def sectionMorphism {C : Type u} [Category.{v} C] (J : Precoverage C)
    (F : Sheaf J.toGrothendieck (Type (max u v w))) (U : C) (t : F.obj.obj (op U)) :
    (presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
      (uliftYoneda.{max u v w, v}.obj U) ⟶ F :=
  ⟨sheafifyLift J.toGrothendieck (uliftYonedaEquiv.symm t) F.property⟩

/-- The image in a point fibre of a section class `[U,x,t]`.
Source: Stacks, Tags 00Y6 and 00Y8 (auxiliary; not a blueprint node). -/
noncomputable def pointSectionImage {C : Type u} [Category.{v} C] (J : Precoverage C)
    (p : GeometricMorphism (Type (max u v w))
      (Sheaf J.toGrothendieck (Type (max u v w))))
    (F : Sheaf J.toGrothendieck (Type (max u v w))) (U : C)
    (x : p.inverse.obj ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
      (uliftYoneda.{max u v w, v}.obj U)))
    (t : F.obj.obj (op U)) : p.inverse.obj F :=
  (p.inverse.map (sectionMorphism J F U t)) x

/-- Section separation by a family of geometric-morphism points implies joint reflection of
isomorphisms. Source: Stacks, Tags 00YK and 00YM, with stalk identifications from Tags 00Y6
and 00Y8 (auxiliary; not a blueprint node).

Proof: composition with a sheaf morphism carries the morphism represented by a section to
that represented by its image, by Yoneda naturality and the universal property of
sheafification. If two sheaf morphisms agree after every inverse image, section separation
therefore makes their values on every section equal. Thus the inverse-image functors are
jointly faithful. Mathlib's criterion for jointly faithful functors from a balanced category
then gives joint reflection of isomorphisms, since sheaves of sets form a balanced category. -/
lemma point_family_conservative
    {C : Type u} [Category.{v} C]
    (J : Precoverage C)
    (I : Type w')
    (p : I → GeometricMorphism (Type (max u v w))
      (Sheaf J.toGrothendieck (Type (max u v w))))
    (hsep : ∀ (F : Sheaf J.toGrothendieck (Type (max u v w)))
      (U : C) (s s' : F.obj.obj (op U)), s ≠ s' →
      ∃ (i : I) (x : (p i).inverse.obj
        ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
          (uliftYoneda.{max u v w, v}.obj U))),
        pointSectionImage J (p i) F U x s ≠ pointSectionImage J (p i) F U x s') :
    JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse) := by
  have hnat (F G : Sheaf J.toGrothendieck (Type (max u v w))) (a : F ⟶ G)
      (U : C) (t : F.obj.obj (op U)) :
      sectionMorphism J F U t ≫ a = sectionMorphism J G U (a.hom.app (op U) t) := by
    apply Sheaf.hom_ext
    dsimp [sectionMorphism]
    rw [← sheafifyLift_comp, uliftYonedaEquiv_symm_comp]
  apply JointlyFaithful.jointlyReflectsIsomorphisms
  refine ⟨?_⟩
  intro F G a b hab
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  by_contra h
  obtain ⟨i, x, hx⟩ := hsep G U.unop (a.hom.app U s) (b.hom.app U s) h
  apply hx
  unfold pointSectionImage
  rw [← hnat F G a U.unop s, ← hnat F G b U.unop s,
    Functor.map_comp, Functor.map_comp, hab i]

end CategoryTheory
