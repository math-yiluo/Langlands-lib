/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Transport of a counit to coefficient systems

Source: the system-counit step of the proper finite-E adjunction proof.
(blueprint: lem-sfb-reduction-system-counit)
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {A B S T : Type*} [Category* A] [Category* B] [Category* S] [Category* T]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
  (redA : A ⥤ S) (redB : B ⥤ T) (P : S ⥤ T) (C : B ⥤ S)
  (e : G ⋙ redA ≅ C) (q : F ⋙ redB ≅ redA ⋙ P)

/-- The counit on actual systems is conjugation of the reduced integral counit
by the two specified comparison isomorphisms. Source: the coherent counit step
of the finite-E proof (blueprint: lem-sfb-reduction-system-counit). -/
def reductionSystemCounit : C ⋙ P ⟶ redB :=
  (Functor.isoWhiskerRight e.symm P).hom ≫
    (Functor.associator G redA P).hom ≫
    (Functor.isoWhiskerLeft G q.symm).hom ≫
    (Functor.associator G F redB).inv ≫
    whiskerRight adj.counit redB ≫ redB.leftUnitor.hom

/-- The conjugated counit satisfies the system-level equation, before any finite
level is evaluated. Source: the coherent counit step of the finite-E proof
(blueprint: lem-sfb-reduction-system-counit).
Proof: expand the constructed natural transformation; the image of the reduction
isomorphism cancels its inverse, and the pushforward comparison cancels its
inverse. The remaining morphism is the reduction of the integral counit. -/
theorem reductionSystemCounit_eq (K : B) :
    q.hom.app (G.obj K) ≫ P.map (e.hom.app K) ≫
        (reductionSystemCounit adj redA redB P C e q).app K =
      redB.map (adj.counit.app K) := by
  simp only [reductionSystemCounit, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Functor.leftUnitor_hom_app, Category.id_comp]
  simp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  rw [← P.map_comp_assoc, e.hom_inv_id_app]
  simp

end CategoryTheory.Adjunction
