/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Localization.Prod

/-! # Descent of a tensor comparison from representatives -/

@[expose] public section
set_option autoImplicit false

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- A tensor comparison descends uniquely when restriction to representatives is fully
faithful and the comparison maps are invertible on representatives and their tensors.
Source: Stacks Project, Categories, Tag 04VK; Cohomology on Sites, Tag 07A4.
(auxiliary; not a blueprint node).
Proof: on the product of representative categories compose the inverse source tensor
identification, the comparison on the tensor, the chain tensor comparison, the target
tensor identification, and the inverse comparisons on each factor. Fully faithful
restriction lifts this natural isomorphism. Cancel the source tensor identification
and the two factor comparisons to prove the square and uniqueness. -/
theorem tensorComparisonDescent
    {K : Type u₁} [Category.{v₁} K] {H : Type u₂} [Category.{v₂} H]
    {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
    (q : K ⥤ D) (q' : H ⥤ E) (F : K ⥤ H) (LF : D ⥤ E)
    (eps : q ⋙ LF ⟶ F ⋙ q')
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hF : ∀ X, P X → S (F.obj X))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory) (D × D) E).obj
      ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful)
    (t : K × K ⥤ K) (t' : H × H ⥤ H)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (r' : (S.ι.prod S.ι) ⋙ t' ⋙ q' ≅ ((S.ι ⋙ q').prod (S.ι ⋙ q')) ⋙ T')
    (b : t ⋙ F ≅ (F.prod F) ⋙ t')
    (he : ∀ X, P X → IsIso (eps.app X))
    (het : ∀ X Y, P X → P Y → IsIso (eps.app (t.obj (X, Y)))) :
    ∃! a : T ⋙ LF ≅ (LF.prod LF) ⋙ T',
      ∀ (X Y : K) (hx : P X) (hy : P Y),
        LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ a.hom.app (q.obj X, q.obj Y) ≫
            T'.map (Prod.mkHom (eps.app X) (eps.app Y)) =
          eps.app (t.obj (X, Y)) ≫ q'.map (b.hom.app (X, Y)) ≫
            r'.hom.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩) := by
  let f := S.lift (P.ι ⋙ F) (fun X ↦ hF X.obj X.property)
  let L := (P.ι ⋙ q).prod (P.ι ⋙ q)
  let e₁ : P.ι ⋙ q ⋙ LF ≅ P.ι ⋙ F ⋙ q' :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (eps.app X.obj) (he X.obj X.property))
      (fun g ↦ eps.naturality g.hom)
  let e₂ : (P.ι.prod P.ι) ⋙ t ⋙ q ⋙ LF ≅
      (P.ι.prod P.ι) ⋙ t ⋙ F ⋙ q' :=
    NatIso.ofComponents
      (fun X ↦ @asIso _ _ _ _ (eps.app (t.obj (X.1.obj, X.2.obj)))
        (het X.1.obj X.2.obj X.1.property X.2.property))
      (fun g ↦ eps.naturality (t.map (Prod.mkHom g.1.hom g.2.hom)))
  let e : L ⋙ (T ⋙ LF) ≅ L ⋙ ((LF.prod LF) ⋙ T') :=
    isoWhiskerRight r.symm LF ≪≫ e₂ ≪≫
      isoWhiskerRight (isoWhiskerLeft (P.ι.prod P.ι) b) q' ≪≫
      isoWhiskerLeft (f.prod f) r' ≪≫ isoWhiskerRight (NatIso.prod e₁.symm e₁.symm) T'
  let a : T ⋙ LF ≅ (LF.prod LF) ⋙ T' := ff.preimageIso e
  have ha (X : P.FullSubcategory × P.FullSubcategory) :
      a.hom.app (L.obj X) = e.hom.app X := by
    exact congrArg (fun z ↦ z.app X) (ff.map_preimage e.hom)
  have hs : ∀ (X Y : K) (hx : P X) (hy : P Y),
      LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ a.hom.app (q.obj X, q.obj Y) ≫
          T'.map (Prod.mkHom (eps.app X) (eps.app Y)) =
        eps.app (t.obj (X, Y)) ≫ q'.map (b.hom.app (X, Y)) ≫
          r'.hom.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩) := by
    intro X Y hx hy
    rw [show a.hom.app (q.obj X, q.obj Y) = e.hom.app (⟨X, hx⟩, ⟨Y, hy⟩) from
      ha (⟨X, hx⟩, ⟨Y, hy⟩)]
    have := he X hx
    have := he Y hy
    change LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫
        (LF.map (r.inv.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫
          eps.app (t.obj (X, Y)) ≫ q'.map (b.hom.app (X, Y)) ≫
          r'.hom.app (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩) ≫
          T'.map (Prod.mkHom (inv (eps.app X)) (inv (eps.app Y)))) ≫
        T'.map (Prod.mkHom (eps.app X) (eps.app Y)) = _
    have hc : Prod.mkHom (inv (eps.app X)) (inv (eps.app Y)) ≫
        Prod.mkHom (eps.app X) (eps.app Y) = 𝟙 _ := by
      ext <;> simp
    simp only [Category.assoc, ← T'.map_comp, hc,
      ← LF.map_comp_assoc, Iso.hom_inv_id_app, LF.map_id, Category.id_comp]
    have hid := T'.map_id ((F ⋙ q').obj X, (F ⋙ q').obj Y)
    rw [hid]
    exact congrArg (fun z ↦ eps.app (t.obj (X, Y)) ≫ q'.map (b.hom.app (X, Y)) ≫ z)
      (Category.comp_id (r'.hom.app
        (⟨F.obj X, hF X hx⟩, ⟨F.obj Y, hF Y hy⟩)))
  refine ⟨a, hs, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply ff.map_injective
  ext X
  obtain ⟨⟨X, hx⟩, ⟨Y, hy⟩⟩ := X
  have := he X hx
  have := he Y hy
  have : IsIso (Prod.mkHom (eps.app X) (eps.app Y)) :=
    ⟨⟨Prod.mkHom (inv (eps.app X)) (inv (eps.app Y)),
      by ext <;> simp, by ext <;> simp⟩⟩
  have h₁ := (ha' X Y hx hy).trans (hs X Y hx hy).symm
  change a'.hom.app (q.obj X, q.obj Y) = a.hom.app (q.obj X, q.obj Y)
  exact (cancel_epi (LF.map (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)))).1
    ((cancel_mono (T'.map (Prod.mkHom (eps.app X) (eps.app Y)))).1
      (by simpa only [Category.assoc] using h₁))

end CategoryTheory
