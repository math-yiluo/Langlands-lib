/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Descent of a normalized functor-square comparison

The general category argument isolates composition and cancellation from the
large concrete representative functors used by integral operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃ uC vC uD vD uE vE uH vH uA vA uB vB uX vX uY vY
open CategoryTheory
namespace CategoryTheory

private theorem isoDescent
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {B : Type u₃} [Category.{v₃} B] (q : C ⥤ D)
    (ff : ((Functor.whiskeringLeft C D B).obj q).FullyFaithful) (F G : D ⥤ B) (H₁ H K₁ K : C ⥤ B)
    (a₁ : q ⋙ F ≅ H₁) (a₂ : H₁ ≅ H) (b₁ : q ⋙ G ≅ K₁) (b₂ : K₁ ≅ K)
    (c : H ≅ K) :
    ∃! α : F ≅ G, ∀ P : C,
      a₁.hom.app P ≫ a₂.hom.app P ≫ c.hom.app P =
        α.hom.app (q.obj P) ≫ b₁.hom.app P ≫ b₂.hom.app P := by
  let e := a₁ ≪≫ a₂ ≪≫ c ≪≫ b₂.symm ≪≫ b₁.symm
  let α : F ≅ G := ff.preimageIso e
  have ha (P : C) : α.hom.app (q.obj P) = e.hom.app P :=
    congrArg (fun z ↦ z.app P) (ff.map_preimage e.hom)
  have hα (P : C) : a₁.hom.app P ≫ a₂.hom.app P ≫ c.hom.app P =
      α.hom.app (q.obj P) ≫ b₁.hom.app P ≫ b₂.hom.app P := by
    rw [ha]
    simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply Iso.ext
  apply ff.map_injective
  ext P
  change β.hom.app (q.obj P) = α.hom.app (q.obj P)
  apply (cancel_mono (b₁.hom.app P ≫ b₂.hom.app P)).mp
  simpa only [Category.assoc] using (hβ P).symm.trans (hα P)

/-- A comparison square on representatives determines a unique comparison after
fully faithful restriction of functors.
Source: Stacks, categories.tex, localization universal property, Tag 04VK.
(blueprint: lem-pur-functor-square-representative-descent).
Proof: on representatives compose the source operation comparison, the source
coefficient comparison, the given chain square, and the inverses of the target
operation and coefficient comparisons. Fully faithful restriction lifts this
natural isomorphism. Its map-preimage equation proves the prescribed square;
cancel the two target isomorphisms and use faithfulness to prove uniqueness. -/
theorem functorSquareRepresentativeDescent
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] {H : Type uH} [Category.{vH} H]
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    (q : C ⥤ D) (p : E ⥤ H) (k : C ⥤ E)
    (t : C ⥤ A) (s : E ⥤ B) (Q : A ⥤ X) (Q' : B ⥤ Y)
    (T : D ⥤ X) (T' : H ⥤ Y) (S : A ⥤ B) (F : X ⥤ Y) (G : D ⥤ H)
    (ff : ((Functor.whiskeringLeft C D Y).obj q).FullyFaithful)
    (r : q ⋙ T ≅ t ⋙ Q) (r' : p ⋙ T' ≅ s ⋙ Q')
    (ε : Q ⋙ F ≅ S ⋙ Q') (η : q ⋙ G ≅ k ⋙ p)
    (c : t ⋙ S ⋙ Q' ≅ k ⋙ s ⋙ Q') :
    ∃! α : T ⋙ F ≅ G ⋙ T', ∀ P : C,
      F.map (r.hom.app P) ≫ ε.hom.app (t.obj P) ≫ c.hom.app P =
        α.hom.app (q.obj P) ≫ T'.map (η.hom.app P) ≫ r'.hom.app (k.obj P) := by
  let a₁ : q ⋙ (T ⋙ F) ≅ t ⋙ Q ⋙ F :=
    NatIso.ofComponents (fun P ↦ F.mapIso (r.app P)) (by
      intro P Q a
      simpa only [Functor.comp_map, Functor.map_comp, Functor.mapIso_hom, Iso.app_hom]
        using congrArg (fun z ↦ F.map z) (r.hom.naturality a))
  let a₂ := Functor.isoWhiskerLeft t ε
  let b₁ : q ⋙ (G ⋙ T') ≅ k ⋙ p ⋙ T' :=
    NatIso.ofComponents (fun P ↦ T'.mapIso (η.app P)) (by
      intro P Q a
      simpa only [Functor.comp_map, Functor.map_comp, Functor.mapIso_hom, Iso.app_hom]
        using congrArg (fun z ↦ T'.map z) (η.hom.naturality a))
  let b₂ := Functor.isoWhiskerLeft k r'
  change ∃! α : T ⋙ F ≅ G ⋙ T', ∀ P : C,
    a₁.hom.app P ≫ a₂.hom.app P ≫ c.hom.app P =
      α.hom.app (q.obj P) ≫ b₁.hom.app P ≫ b₂.hom.app P
  exact isoDescent q ff _ _ _ _ _ _ a₁ a₂ b₁ b₂ c

end CategoryTheory
