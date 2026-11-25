/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence
public import WeilConjectures.CategoryTheory.Adjunction.MateCompose

/-!
# Units of adjunctions and conjugate isomorphisms

Compatibilities of the units of adjunctions with conjugates (`conjugateIsoEquiv`) and mates of
natural isomorphisms, for adjunctions transported along equivalences.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
      (adj₂ : L₂ ⊣ R₂)
  (G : A ≌ C) (H : B ≌ D)

/-- The exchange isomorphism `L₁ ⋙ H ≅ G ⋙ L₂` of left adjoints obtained by conjugation
    from an
exchange isomorphism `H⁻¹ ⋙ R₁ ≅ R₂ ⋙ G⁻¹` of the right adjoints is characterized
by the
units: its inverse transposes to `G η₁ ≫ d`,
for `d : R₁ ⋙ G ≅ H ⋙ R₂` inducing `d'`. -/
theorem unit_app_comp_map_conjugateIsoEquiv_symm_inv_app (d : R₁ ⋙ G.functor ≅ H.functor ⋙
R₂)
    (d' : H.inverse ⋙ R₁ ≅ R₂ ⋙ G.inverse)
    (hd' : ∀ b : D, d'.hom.app b = G.unitIso.hom.app (R₁.obj (H.inverse.obj b)) ≫
      G.inverse.map (d.hom.app (H.inverse.obj b) ≫ R₂.map (H.counitIso.hom.app b)))
    (a : A) :
    adj₂.unit.app (G.functor.obj a) ≫
        R₂.map (((conjugateIsoEquiv (adj₁.comp H.toAdjunction)
          (G.toAdjunction.comp adj₂)).symm d').hom.app a) =
      G.functor.map (adj₁.unit.app a) ≫ d.hom.app (L₁.obj a) := by
  have h := unit_conjugateEquiv_symm (adj₁.comp H.toAdjunction) (G.toAdjunction.comp adj₂)
    d'.hom a
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, hd'] at h
  have hn := d.hom.naturality (H.unit.app (L₁.obj a))
  simp only [Functor.comp_map] at hn
  have h' : G.unit.app a ≫ G.inverse.map
      (G.functor.map (adj₁.unit.app a ≫ R₁.map (H.unit.app (L₁.obj a))) ≫
        d.hom.app (H.inverse.obj ((L₁ ⋙ H.functor).obj a)) ≫
          R₂.map (H.counitIso.hom.app ((L₁ ⋙ H.functor).obj a))) =
      G.unit.app a ≫ G.inverse.map (adj₂.unit.app (G.functor.obj a) ≫
        R₂.map (((conjugateEquiv (adj₁.comp H.toAdjunction) (G.toAdjunction.comp adj₂)).symm
          d'.hom).app a)) := by
    rw [Functor.map_comp, ← Category.assoc]
    erw [G.unit_naturality]
    simp only [Category.assoc, Functor.comp_map, Functor.map_comp,
      Equivalence.toAdjunction_unit] at h ⊢
    exact h
  have h3 := G.inverse.map_injective ((cancel_epi (G.unit.app a)).1 h')
  rw [conjugateIsoEquiv_symm_apply_hom, ← h3, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [
    ← R₂.map_comp]
  erw [Equivalence.functor_unit_comp]
  rw [R₂.map_id, Category.comp_id]

section Compose

variable {A B C A' B' C' : Type*} [Category A] [Category B] [Category C] [Category A']
  [Category B'] [Category C']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : A ⥤ C} {R₃ : C
      ⥤ A}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'} {L₃' : A' ⥤
      C'}
  {R₃' : C' ⥤ A'}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₁' : L₁' ⊣
      R₁') (adj₂' : L₂' ⊣ R₂')
  (adj₃' : L₃' ⊣ R₃') (e : L₃ ≅ L₁ ⋙ L₂) (e' : L₃' ≅ L₁' ⋙ L₂')
  {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
  (ν₁ : G ⋙ L₁' ⟶ L₁ ⋙ H) (ν₂ : H ⋙ L₂' ⟶ L₂ ⋙ K) (ν₃ : G ⋙ L₃'
      ⟶ L₃ ⋙ K)

/-- **Converse of the composition law for mates**: if the mates of exchange transformations
satisfy the composition law under the conjugate isomorphisms of `e` and `e'`, then the exchange
transformations themselves are composed under `e` and `e'`. -/
theorem app_comp_map_hom_app_of_mateEquiv
    (hm : ∀ c : C, (mateEquiv adj₃ adj₃' ν₃).app c ≫
        (conjugateIsoEquiv adj₃' (adj₁'.comp adj₂') e'.symm).hom.app (K.obj c) =
      G.map ((conjugateIsoEquiv adj₃ (adj₁.comp adj₂) e.symm).hom.app c) ≫
        (mateEquiv adj₁ adj₁' ν₁).app (R₂.obj c) ≫
            R₁'.map ((mateEquiv adj₂ adj₂' ν₂).app c))
    (a : A) :
    ν₃.app a ≫ K.map (e.hom.app a) =
      e'.hom.app (G.obj a) ≫ L₂'.map (ν₁.app a) ≫ ν₂.app (L₁.obj a) := by
  let ν₃' : G ⋙ L₃' ⟶ L₃ ⋙ K :=
    Functor.whiskerLeft G e'.hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ν₁ L₂' ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L₁ ν₂ ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight e.inv K
  have hν₃' (a : A) : ν₃'.app a ≫ K.map (e.hom.app a) =
      e'.hom.app (G.obj a) ≫ L₂'.map (ν₁.app a) ≫ ν₂.app (L₁.obj a) := by
    simp [ν₃', ← K.map_comp]
  have hm' := mateEquiv_app_comp_conjugateIsoEquiv_hom_app adj₁ adj₂ adj₃ adj₁' adj₂'
      adj₃' e e'
    ν₁ ν₂ ν₃' hν₃'
  have hmate : mateEquiv adj₃ adj₃' ν₃ = mateEquiv adj₃ adj₃' ν₃' := by
    ext c
    exact (cancel_mono _).1 ((hm c).trans (hm' c).symm)
  rw [(mateEquiv adj₃ adj₃').injective hmate]
  exact hν₃' a

end Compose

section InverseComp

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {R₁ : B ⥤ A} {R₂ : D ⥤ C} (G : A ≌ C) (H : B ≌ D)

/-- The components of the exchange isomorphism `H⁻¹ ⋙ R₁ ≅ R₂ ⋙ G⁻¹` induced by an
    exchange
isomorphism `d : R₁ ⋙ G ≅ H ⋙ R₂` and the unit and counit of the equivalences. -/
lemma inverseCompIso_hom_app (d : R₁ ⋙ G.functor ≅ H.functor ⋙ R₂) (b : D) :
    ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft (H.inverse ⋙ R₁) G.unitIso
        ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm
          ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight d _) ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm
          ≪≫
      Functor.isoWhiskerRight H.counitIso (R₂ ⋙ G.inverse) ≪≫ Functor.leftUnitor
          _).hom.app b =
      G.unitIso.hom.app (R₁.obj (H.inverse.obj b)) ≫
        G.inverse.map (d.hom.app (H.inverse.obj b) ≫ R₂.map (H.counitIso.hom.app b)) := by
  simp

end InverseComp

end CategoryTheory
