/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Pasting invertible squares of adjoints
Source: Mathlib's conjugation identities; Stacks Project, Tag 0D5S.
(blueprint: lem-pc-adjunction-square-composition). -/

@[expose] public section
open CategoryTheory Functor
namespace CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem conjugateIso_trans
    {A B : Type*} [Category* A] [Category* B]
    {L₁ L₂ L₃ : A ⥤ B} {R₁ R₂ R₃ : B ⥤ A}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (e : L₂ ≅ L₁) (f : L₃ ≅ L₂) :
    conjugateIsoEquiv a₁ a₃ (f ≪≫ e) =
      conjugateIsoEquiv a₁ a₂ e ≪≫ conjugateIsoEquiv a₂ a₃ f := by
  ext : 1
  exact (conjugateEquiv_comp a₁ a₂ a₃ e.hom f.hom).symm

private theorem conjugateIso_symm
    {A B : Type*} [Category* A] [Category* B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁) :
    conjugateIsoEquiv a₂ a₁ e.symm = (conjugateIsoEquiv a₁ a₂ e).symm := rfl

private theorem conjugateIso_whiskerLeft
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {L : A ⥤ B} {R : B ⥤ A} {L₁ L₂ : B ⥤ C} {R₁ R₂ : C ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R) (e : L₂ ≅ L₁) :
    conjugateIsoEquiv (a.comp a₁) (a.comp a₂) (isoWhiskerLeft L e) =
      isoWhiskerRight (conjugateIsoEquiv a₁ a₂ e) R := by
  ext : 1
  exact conjugateEquiv_whiskerLeft a₁ a₂ a e.hom

private theorem conjugateIso_whiskerRight
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R) (e : L₂ ≅ L₁) :
    conjugateIsoEquiv (a₁.comp a) (a₂.comp a) (isoWhiskerRight e L) =
      isoWhiskerLeft R (conjugateIsoEquiv a₁ a₂ e) := by
  ext : 1
  exact conjugateEquiv_whiskerRight a₁ a₂ a e.hom

private theorem conjugateIso_associator
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) :
    conjugateIsoEquiv (a₁.comp (a₂.comp a₃)) ((a₁.comp a₂).comp a₃)
      (associator L₁ L₂ L₃) = associator R₃ R₂ R₁ := by
  ext : 1
  exact conjugateEquiv_associator_hom a₁ a₂ a₃

/-- Pasting two invertible right-adjoint squares gives the pasted left-adjoint square.
Source: Mathlib `conjugateEquiv_comp`, its whiskering formulas and associator formula.
(blueprint: lem-pc-adjunction-square-composition).
Proof: conjugate both paths by the composite adjunctions. Conjugation reverses
composition and exchanges left and right whiskering. The assumed right-square
identity then identifies the paths; its adjacent comparison inverses cancel. -/
theorem adjunctionSquareComposition
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {La : A ⥤ D} {Ra : D ⥤ A} {Lb : B ⥤ E} {Rb : E ⥤ B}
    {Lc : C ⥤ F} {Rc : F ⥤ C}
    {H : A ⥤ B} {S : B ⥤ A} {I : B ⥤ C} {T : C ⥤ B}
    {J : A ⥤ C} {U : C ⥤ A}
    {P : D ⥤ E} {Rp : E ⥤ D} {Q : E ⥤ F} {Rq : F ⥤ E}
    {R : D ⥤ F} {Rr : F ⥤ D}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc)
    (h : H ⊣ S) (i : I ⊣ T) (j : J ⊣ U)
    (p : P ⊣ Rp) (q : Q ⊣ Rq) (r : R ⊣ Rr)
    (α01 : Rp ⋙ Ra ≅ Rb ⋙ S) (α12 : Rq ⋙ Rb ≅ Rc ⋙ T)
    (α02 : Rr ⋙ Ra ≅ Rc ⋙ U) (β : U ≅ T ⋙ S) (γ : Rq ⋙ Rp ≅ Rr)
    (θ01 : La ⋙ P ≅ H ⋙ Lb) (θ12 : Lb ⋙ Q ≅ I ⋙ Lc)
    (θ02 : La ⋙ R ≅ J ⋙ Lc) (μ : J ≅ H ⋙ I) (κ : P ⋙ Q ≅ R)
    (h01 : conjugateIsoEquiv (h.comp b) (a.comp p) θ01 = α01.symm)
    (h12 : conjugateIsoEquiv (i.comp c) (b.comp q) θ12 = α12.symm)
    (h02 : conjugateIsoEquiv (j.comp c) (a.comp r) θ02 = α02.symm)
    (hμ : conjugateIsoEquiv (h.comp i) j μ = β.symm)
    (hκ : conjugateIsoEquiv r (p.comp q) κ = γ.symm)
    (hr : α02 = isoWhiskerRight γ.symm Ra ≪≫ associator Rq Rp Ra ≪≫
      isoWhiskerLeft Rq α01 ≪≫ (associator Rq Rb S).symm ≪≫
      isoWhiskerRight α12 S ≪≫ associator Rc T S ≪≫ isoWhiskerLeft Rc β.symm) :
    isoWhiskerRight θ01 Q ≪≫ associator H Lb Q ≪≫ isoWhiskerLeft H θ12 ≪≫
        (associator H I Lc).symm =
      associator La P Q ≪≫ isoWhiskerLeft La κ ≪≫ θ02 ≪≫ isoWhiskerRight μ Lc := by
  apply (conjugateIsoEquiv ((h.comp i).comp c) ((a.comp p).comp q)).injective
  rw [conjugateIso_trans _ ((h.comp b).comp q) _,
    conjugateIso_trans _ (h.comp (b.comp q)) _,
    conjugateIso_trans _ (h.comp (i.comp c)) _]
  rw [conjugateIso_trans _ (a.comp (p.comp q)) _,
    conjugateIso_trans _ (a.comp r) _, conjugateIso_trans _ (j.comp c) _]
  simp only [conjugateIso_symm, conjugateIso_associator,
    conjugateIso_whiskerLeft, conjugateIso_whiskerRight, h01, h12, h02, hμ, hκ]
  rw [hr]
  apply Iso.ext
  simp [Iso.trans_symm]

end CategoryTheory
