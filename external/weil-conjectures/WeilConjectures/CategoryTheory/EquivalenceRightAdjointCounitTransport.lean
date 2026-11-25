/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Counit transport along an equivalence -/
@[expose] public section
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Transport right adjoints along an equivalence and a comparison of left adjoints.
Source: Stacks Project, Tag 0D5S; uniqueness of adjoints.
(blueprint: lem-cat-equivalence-right-adjoint-counit-transport)

Proof: Form the comparison j from e.inverse followed by P to Q by whiskering
p inverse with e.inverse, then applying the counit isomorphism of e. Compose
the adjunction e.symm.toAdjunction with ac, and transport its left functor along
j. This yields an adjunction Q to c followed by e.functor. Its counit at Z is
j inverse at e(c(Z)), then P of the inverse unit of e, then ac counit. Naturality
of p and the triangle identity of the equivalence reduce this to p at c(Z)
followed by ac counit. Right adjoint uniqueness against ad gives t, and the
counit identity for rightAdjointUniq proves the assertion. This works without
nonemptiness assumptions on any category. -/
private theorem transport
    {E J T : Type*} [Category* E] [Category* J] [Category* T]
    (e : E ≌ J)
    {P : E ⥤ T} {Q : J ⥤ T} {c : T ⥤ E} {d : T ⥤ J}
    (ac : P ⊣ c) (ad : Q ⊣ d) (p : e.functor ⋙ Q ≅ P) :
    ∃ t : c ⋙ e.functor ≅ d, ∀ Z : T,
      Q.map (t.hom.app Z) ≫ ad.counit.app Z =
        p.hom.app (c.obj Z) ≫ ac.counit.app Z := by
  classical
  let j : e.inverse ⋙ P ≅ Q :=
    Functor.isoWhiskerLeft e.inverse p.symm ≪≫
      (Functor.associator e.inverse e.functor Q).symm ≪≫
      Functor.isoWhiskerRight e.counitIso Q ≪≫ Functor.leftUnitor Q
  let a : Q ⊣ c ⋙ e.functor := (e.symm.toAdjunction.comp ac).ofNatIsoLeft j
  refine ⟨a.rightAdjointUniq ad, fun Z ↦ ?_⟩
  rw [Adjunction.rightAdjointUniq_hom_app_counit]
  change j.inv.app (e.functor.obj (c.obj Z)) ≫
    (e.symm.toAdjunction.comp ac).counit.app Z = _
  rw [Adjunction.comp_counit_app]
  change j.inv.app (e.functor.obj (c.obj Z)) ≫
    P.map (e.unitIso.inv.app (c.obj Z)) ≫ ac.counit.app Z = _
  dsimp [j]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← p.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc]
  simp

/-- The functor form of counit transport along an equivalence.
Source: Stacks Project, Tag 0D5S; uniqueness of adjoints.
(blueprint: lem-cat-equivalence-right-adjoint-counit-transport)

Proof: Apply the preceding equivalence calculation to L.asEquivalence, whose
functor is definitionally L. The calculation composes adjunctions and applies
rightAdjointUniq; naturality of p and the equivalence triangle identity identify
the resulting counit with p followed by the original counit. -/
theorem equivalence_rightAdjoint_counit_transport
    {E J T : Type*} [Category* E] [Category* J] [Category* T]
    (L : E ⥤ J) [L.IsEquivalence]
    {P : E ⥤ T} {Q : J ⥤ T} {c : T ⥤ E} {d : T ⥤ J}
    (ac : P ⊣ c) (ad : Q ⊣ d) (p : L ⋙ Q ≅ P) :
    ∃ t : c ⋙ L ≅ d, ∀ Z : T,
      Q.map (t.hom.app Z) ≫ ad.counit.app Z =
        p.hom.app (c.obj Z) ≫ ac.counit.app Z := by
  classical
  exact transport L.asEquivalence ac ad p
