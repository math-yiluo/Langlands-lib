/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Comparisons normalized on functorial resolutions

Source: Stacks Project, Tag 0D6E; the resolution argument for uniqueness of derived functors.
(blueprint: lem-pur-resolution-normalized-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace CategoryTheory.Localization

/-- Two transformations which become isomorphisms on functorial resolutions determine
one normalized isomorphism after localization.
Source: Stacks Project, Tag 0D6E
(blueprint: lem-pur-resolution-normalized-comparison).
Proof: on a resolution invert the first transformation and follow it by the second.
Conjugate by the localized resolution maps, which are invertible. Full faithfulness
of precomposition with localization descends this isomorphism. Naturality along the
resolution map proves normalization on every object. For uniqueness, cancel the
first transformation on a resolution, and then cancel the localized resolution map;
essential surjectivity of localization proves equality. -/
private theorem resolutionNormalizedComparison_aux
    {C D H : Type*} [Category C] [Category D] [Category H]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (P : C ⥤ C) (q : 𝟭 C ⟶ P) (hq : ∀ X, W (q.app X))
    (O : C ⥤ H) (S T : D ⥤ H) (α : O ⟶ Q ⋙ S) (β : O ⟶ Q ⋙ T)
    (hα : ∀ X, IsIso (α.app (P.obj X))) (hβ : ∀ X, IsIso (β.app (P.obj X))) :
    ∃! e : S ≅ T, ∀ X, α.app X ≫ e.hom.app (Q.obj X) = β.app X := by
  have hqQ (X : C) : IsIso (Q.map (q.app X)) := inverts Q W _ (hq X)
  let a := Functor.whiskerLeft P α
  let b := Functor.whiskerLeft P β
  have ha (X : C) : IsIso (a.app X) := hα X
  have hb (X : C) : IsIso (b.app X) := hβ X
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let s := Functor.whiskerRight q (Q ⋙ S)
  let t := Functor.whiskerRight q (Q ⋙ T)
  have hs (X : C) : IsIso (s.app X) := by
    change IsIso (S.map (Q.map (q.app X)))
    infer_instance
  have ht (X : C) : IsIso (t.app X) := by
    change IsIso (T.map (Q.map (q.app X)))
    infer_instance
  have : IsIso s := NatIso.isIso_of_isIso_app s
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let eQ : Q ⋙ S ≅ Q ⋙ T := asIso s ≪≫ (asIso a).symm ≪≫ asIso b ≪≫ (asIso t).symm
  let ff := fullyFaithfulWhiskeringLeft Q W H
  let e : S ≅ T := ff.preimageIso eQ
  have he (X : C) : e.hom.app (Q.obj X) = eQ.hom.app X :=
    congr_app (ff.map_preimage eQ.hom) X
  have hn (X : C) : α.app X ≫ e.hom.app (Q.obj X) = β.app X := by
    rw [he]
    simp only [eQ, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      NatTrans.comp_app, NatIso.isIso_inv_app]
    change α.app X ≫ S.map (Q.map (q.app X)) ≫ inv (α.app (P.obj X)) ≫
      β.app (P.obj X) ≫ inv (T.map (Q.map (q.app X))) = β.app X
    rw [← reassoc_of% (α.naturality (q.app X))]
    simp only [Functor.id_obj, IsIso.hom_inv_id_assoc]
    rw [reassoc_of% (β.naturality (q.app X))]
    simp
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply natTrans_ext Q W
  intro X
  apply (cancel_mono (T.map (Q.map (q.app X)))).1
  rw [← e'.hom.naturality, ← e.hom.naturality]
  congr 1
  apply (cancel_epi (α.app (P.obj X))).1
  exact (he' (P.obj X)).trans (hn (P.obj X)).symm

/-- A specified model isomorphism may be retained in the normalization equation.
Source: Stacks Project, Tag 0D6E
(blueprint: lem-pur-resolution-normalized-comparison).
Proof: compose the second transformation with the inverse of the model isomorphism.
The resolution comparison lemma descends the resulting unique isomorphism through
localization. Postcomposition with the model isomorphism gives the stated equation;
cancelling it proves the converse equation and uniqueness. -/
theorem resolutionNormalizedComparison
    {C D H : Type*} [Category C] [Category D] [Category H]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (P : C ⥤ C) (q : 𝟭 C ⟶ P) (hq : ∀ X, W (q.app X))
    (O : C ⥤ H) (S T : D ⥤ H) (U : C ⥤ H) (κ : Q ⋙ T ≅ U)
    (α : O ⟶ Q ⋙ S) (β : O ⟶ U)
    (hα : ∀ X, IsIso (α.app (P.obj X))) (hβ : ∀ X, IsIso (β.app (P.obj X))) :
    ∃! e : S ≅ T, ∀ X,
      α.app X ≫ e.hom.app (Q.obj X) ≫ κ.hom.app X = β.app X := by
  let β' : O ⟶ Q ⋙ T := β ≫ κ.inv
  have hβ' (X : C) : IsIso (β'.app (P.obj X)) := by
    dsimp only [β', NatTrans.comp_app]
    infer_instance
  obtain ⟨e, he, huniq⟩ := resolutionNormalizedComparison_aux
    Q W P q hq O S T α β' hα hβ'
  have hnorm (e : S ≅ T) :
      (∀ X, α.app X ≫ e.hom.app (Q.obj X) = β'.app X) ↔
        (∀ X, α.app X ≫ e.hom.app (Q.obj X) ≫ κ.hom.app X = β.app X) := by
    constructor
    · intro h X
      rw [← Category.assoc, h X]
      simp only [β', NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    · intro h X
      apply (cancel_mono (κ.hom.app X)).1
      simpa only [β', NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app,
        Category.comp_id] using h X
  exact ⟨e, (hnorm e).1 he, fun e' he' ↦ huniq e' ((hnorm e').2 he')⟩

end CategoryTheory.Localization
