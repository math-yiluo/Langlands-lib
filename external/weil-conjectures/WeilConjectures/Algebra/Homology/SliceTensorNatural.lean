/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Natural tensor comparison for continuous cocontinuous restriction

Source: Stacks Project, Tags 01CD and 03DH.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SheafOfModules

/-- Composing four commutative squares gives the outer commutative rectangle. -/
theorem compose_four_squares {D : Type*} [Category* D]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    (a₀ : A₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
    (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃) (b₃ : B₃ ⟶ B₄)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (f₃ : A₃ ⟶ B₃) (f₄ : A₄ ⟶ B₄)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (h₂ : f₂ ≫ b₂ = a₂ ≫ f₃) (h₃ : f₃ ≫ b₃ = a₃ ≫ f₄) :
    f₀ ≫ (b₀ ≫ b₁ ≫ b₂ ≫ b₃) = (a₀ ≫ a₁ ≫ a₂ ≫ a₃) ≫ f₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- A commutative square of isomorphisms also commutes with the inverses. -/
theorem inverse_square {D : Type*} [Category* D]
    {A B A' B' : D} (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- The tensor/sheafification comparison is natural in both module arguments. -/
theorem tensorObjIsoSheafification_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification (R := R) M' N').hom =
      (tensorObjIsoSheafification (R := R) M N).hom ≫
        (PresheafOfModules.sheafification.{u}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
            (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  rw [tensorHom_def, Category.assoc, whiskerLeft_tensorObjIsoSheafification_hom,
    ← Category.assoc, whiskerRight_tensorObjIsoSheafification_hom,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

/-- Tensoring two commutative squares of isomorphisms gives a commutative square. -/
theorem tensor_square {D : Type*} [Category* D] [MonoidalCategory D]
    {M N M' N' P Q P' Q' : D} (f : M ⟶ M') (g : N ⟶ N')
    (f' : P ⟶ P') (g' : Q ⟶ Q')
    (a : M ≅ P) (b : N ≅ Q) (a' : M' ≅ P') (b' : N' ≅ Q')
    (ha : f ≫ a'.hom = a.hom ≫ f') (hb : g ≫ b'.hom = b.hom ≫ g') :
    (f ⊗ₘ g) ≫ (a' ⊗ᵢ b').hom = (a ⊗ᵢ b).hom ≫ (f' ⊗ₘ g') := by
  simp only [tensorIso_hom, tensorHom_comp_tensorHom, ha, hb]

/-- Presheaf tensor restriction is the inverse monoidal structure map.
Source: Stacks 01CD (auxiliary; not a blueprint node). -/
noncomputable def slicePresheafTensorIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pushforward₀OfCommRingCat F R).obj (M ⊗ N) ≅
      (PresheafOfModules.pushforward₀OfCommRingCat F R).obj M ⊗
        (PresheafOfModules.pushforward₀OfCommRingCat F R).obj N :=
  (Functor.Monoidal.μIso (PresheafOfModules.pushforward₀OfCommRingCat F R) M N).symm

private theorem slicePresheafTensorIso_natural
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    {M M' N N' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.pushforward₀OfCommRingCat F R).map (f ⊗ₘ g) ≫
        (slicePresheafTensorIso F R M' N').hom =
      (slicePresheafTensorIso F R M N).hom ≫
        ((PresheafOfModules.pushforward₀OfCommRingCat F R).map f ⊗ₘ
          (PresheafOfModules.pushforward₀OfCommRingCat F R).map g) :=
  (Functor.OplaxMonoidal.δ_natural _ f g).symm

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
  (R : Sheaf K CommRingCat.{u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R

set_option hygiene false in
set_option quotPrecheck false in
local notation "R'" => (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R

/-- The restriction functor with its commutative coefficient sheaf written explicitly.
This fixes the codomain presentation before installing the monoidal structure.
Source: Stacks 04IX (auxiliary; not a blueprint node). -/
noncomputable abbrev sliceCommModuleRestriction :
    SheafOfModules.{u} A ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj (R')) :=
  sliceModuleRestriction (J := J) F A

/-- The underlying module presheaf of continuous restriction.
Source: Stacks 04IX (auxiliary; not a blueprint node). -/
noncomputable def sliceRestrictionUnderlyingIso (M : SheafOfModules.{u} A) :
    (PresheafOfModules.pushforward₀.{u} F (A).obj).obj M.val ≅
      ((sliceCommModuleRestriction (J := J) F R).obj M).val :=
  PresheafOfModules.isoMk (fun W ↦
    (ModuleCat.restrictScalarsId'App
      (RingHom.id ((A).obj.obj (F.op.obj W)))
      (by rfl) (M.val.obj (F.op.obj W))).symm)
    (by intros; ext x; rfl)

omit [F.IsCocontinuous J K] in
private theorem sliceRestrictionUnderlyingIso_natural
    {M N : SheafOfModules.{u} A} (f : M ⟶ N) :
    (PresheafOfModules.pushforward₀.{u} F (A).obj).map f.val ≫
        (sliceRestrictionUnderlyingIso (J := J) F R N).hom =
      (sliceRestrictionUnderlyingIso (J := J) F R M).hom ≫
        ((sliceCommModuleRestriction (J := J) F R).map f).val := by
  ext W x
  rfl

/-- Canonical tensor comparison induced by presheaf restriction and sheafification.
Source: Stacks 01CD and 03DH (auxiliary; not a blueprint node). -/
@[irreducible] noncomputable def sliceTensorIso (M N : SheafOfModules.{u} A) :
    letI := monoidalCategory R
    letI := monoidalCategory (R')
    (sliceCommModuleRestriction (J := J) F R).obj (M ⊗ N) ≅
      (sliceCommModuleRestriction (J := J) F R).obj M ⊗
        (sliceCommModuleRestriction (J := J) F R).obj N := by
  let V := sliceCommModuleRestriction (J := J) F R
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj (R')
  let P : PresheafOfModules.{u} (A).obj ⥤ PresheafOfModules.{u} B.obj :=
    PresheafOfModules.pushforward₀OfCommRingCat F R.obj
  let S := PresheafOfModules.sheafification.{u} (R := A) (𝟙 (A).obj)
  let T := PresheafOfModules.sheafification.{u} (R := B) (𝟙 B.obj)
  let := monoidalCategory R
  letI := monoidalCategory (R')
  let i : S ⋙ V ≅ P ⋙ T := sliceSheafificationIso (J := J) F A
  let j (M : SheafOfModules.{u} A) : P.obj M.val ≅ (V.obj M).val :=
    sliceRestrictionUnderlyingIso (J := J) F R M
  exact V.mapIso (tensorObjIsoSheafification (R := R) M N) ≪≫
    i.app (M.val ⊗ N.val) ≪≫
    T.mapIso (slicePresheafTensorIso F R.obj M.val N.val) ≪≫
    T.mapIso (j M ⊗ᵢ j N) ≪≫
    (tensorObjIsoSheafification (R := R') (V.obj M) (V.obj N)).symm

/-- Tensor restriction is natural in both module arguments.
Source: Stacks 01CD and 03DH (auxiliary; not a blueprint node).
Proof: Compose the naturality squares for tensor sheafification, continuous
sheafification restriction, presheaf tensor restriction, and the underlying
restriction comparison, then invert the final tensor-sheafification square. -/
theorem sliceTensorIso_natural
    {M M' N N' : SheafOfModules.{u} A} (f : M ⟶ M') (g : N ⟶ N') :
    letI := monoidalCategory R
    let := monoidalCategory (R')
    (sliceCommModuleRestriction (J := J) F R).map (f ⊗ₘ g) ≫
        (sliceTensorIso (J := J) F R M' N').hom =
      (sliceTensorIso (J := J) F R M N).hom ≫
        ((sliceCommModuleRestriction (J := J) F R).map f ⊗ₘ
          (sliceCommModuleRestriction (J := J) F R).map g) := by
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj (R')
  let V := sliceCommModuleRestriction (J := J) F R
  let P : PresheafOfModules.{u} (A).obj ⥤ PresheafOfModules.{u} B.obj :=
    PresheafOfModules.pushforward₀OfCommRingCat F R.obj
  let S := PresheafOfModules.sheafification.{u} (R := A) (𝟙 (A).obj)
  let T := PresheafOfModules.sheafification.{u} (R := B) (𝟙 B.obj)
  let := monoidalCategory R
  let := monoidalCategory (R')
  let sourcePresheafMonoidal : MonoidalCategory (PresheafOfModules.{u} (A).obj) :=
    inferInstanceAs (MonoidalCategory
      (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)))
  let targetPresheafMonoidal : MonoidalCategory (PresheafOfModules.{u} B.obj) :=
    inferInstanceAs (MonoidalCategory
      (PresheafOfModules.{u} ((R').obj ⋙ forget₂ CommRingCat RingCat)))
  let targetSheafMonoidal : MonoidalCategory (SheafOfModules.{u} B) := monoidalCategory (R')
  let i : S ⋙ V ≅ P ⋙ T := sliceSheafificationIso (J := J) F A
  let j (M : SheafOfModules.{u} A) : P.obj M.val ≅ (V.obj M).val :=
    sliceRestrictionUnderlyingIso (J := J) F R M
  let pq : P.obj M.val ⊗ P.obj N.val ⟶ P.obj M'.val ⊗ P.obj N'.val :=
    @tensorHom (PresheafOfModules.{u} B.obj) _
      targetPresheafMonoidal.toMonoidalCategoryStruct _ _ _ _ (P.map f.val) (P.map g.val)
  simp only [sliceTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  apply compose_four_squares
    (V.map (tensorObjIsoSheafification (R := R) M N).hom)
    (i.hom.app (M.val ⊗ N.val))
    (T.map (slicePresheafTensorIso F R.obj M.val N.val).hom)
    (T.map (j M ⊗ᵢ j N).hom ≫
      (tensorObjIsoSheafification (R := R') (V.obj M) (V.obj N)).inv)
    (V.map (tensorObjIsoSheafification (R := R) M' N').hom)
    (i.hom.app (M'.val ⊗ N'.val))
    (T.map (slicePresheafTensorIso F R.obj M'.val N'.val).hom)
    (T.map (j M' ⊗ᵢ j N').hom ≫
      (tensorObjIsoSheafification (R := R') (V.obj M') (V.obj N')).inv)
    (V.map (f ⊗ₘ g)) (V.map (S.map (f.val ⊗ₘ g.val)))
    (T.map (P.map (f.val ⊗ₘ g.val))) (T.map pq)
    (V.map f ⊗ₘ V.map g)
  · simpa only [Functor.map_comp] using
      congrArg V.map (tensorObjIsoSheafification_natural R f g)
  · exact i.hom.naturality (f.val ⊗ₘ g.val)
  · simpa only [P, pq, Functor.map_comp] using congrArg T.map
      (slicePresheafTensorIso_natural F R.obj f.val g.val)
  · have ht := tensor_square (P.map f.val) (P.map g.val)
      (V.map f).val (V.map g).val
      (j M) (j N)
      (j M') (j N')
      (sliceRestrictionUnderlyingIso_natural (J := J) F R f)
      (sliceRestrictionUnderlyingIso_natural (J := J) F R g)
    have hi := inverse_square
      (tensorObjIsoSheafification (R := R') (V.obj M) (V.obj N))
      (tensorObjIsoSheafification (R := R') (V.obj M') (V.obj N'))
      (V.map f ⊗ₘ V.map g) (T.map ((V.map f).val ⊗ₘ (V.map g).val))
      (tensorObjIsoSheafification_natural (R') (V.map f) (V.map g))
    dsimp only [pq]
    rw [← T.map_comp_assoc, ht, T.map_comp_assoc, hi, Category.assoc]

end SheafOfModules
