/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.SpectralObject
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic

/-!
# Spectral objects in abelian categories from triangulated spectral objects

Let `X : Triangulated.SpectralObject C ι` be a spectral object in a pretriangulated
category `C`, and `F : C ⥤ A` a homological functor to an abelian category `A`
equipped with a shift sequence `F.ShiftSequence ℤ`. In this file, we construct
`X.mapHomologicalFunctor F : Abelian.SpectralObject A ι`: its functors are
`H n := X.ω₁ ⋙ F.shift n`, and the connecting homomorphisms are given by the
connecting homomorphisms `F.homologySequenceδ` of the long exact sequences obtained
by applying `F` to the functorial distinguished triangles `X.ω₂`.

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Triangulated.SpectralObject

variable {C ι A : Type*} [Category* C] [Category* ι] [Category* A] [Abelian A]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] (X : SpectralObject C ι) (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

end Triangulated.SpectralObject

namespace Triangulated.SpectralObject

variable {C ι : Type*} [Category* C] [Category* ι] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Constructor for isomorphisms of spectral objects in a pretriangulated category: an
isomorphism `X.ω₁ ≅ Y.ω₁` which commutes with the connecting homomorphisms. -/
@[simps]
def isoMk {X Y : SpectralObject C ι} (e : X.ω₁ ≅ Y.ω₁)
    (comm : ∀ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k),
      X.δ f g ≫ (e.hom.app (mk₁ f))⟦(1 : ℤ)⟧' = e.hom.app (mk₁ g) ≫ Y.δ f g) :
    X ≅ Y where
  hom := { hom := e.hom, comm := comm }
  inv :=
    { hom := e.inv
      comm f g := by
        rw [← cancel_epi (e.hom.app (mk₁ g)), ← reassoc_of% (comm f g), ← Functor.map_comp,
          Iso.hom_inv_id_app, Functor.map_id, Category.comp_id, Iso.hom_inv_id_app_assoc] }
  hom_inv_id := SpectralObject.hom_ext e.hom_inv_id
  inv_hom_id := SpectralObject.hom_ext e.inv_hom_id

end Triangulated.SpectralObject

namespace Functor

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The functor from spectral objects in a pretriangulated category `C` to spectral
objects in an abelian category `A` that is induced by a homological functor `F : C ⥤ A`
equipped with a shift sequence. -/
noncomputable def mapHomologicalSpectralObject (F : C ⥤ A) [F.IsHomological]
    [F.ShiftSequence ℤ] (ι : Type*) [Category* ι] :
    Triangulated.SpectralObject C ι ⥤ Abelian.SpectralObject A ι where
  obj X := X.mapHomologicalFunctor F
  map α :=
    { hom n := Functor.whiskerRight α.hom (F.shift n)
      comm n₀ n₁ h i j k f g := by
        simp only [Triangulated.SpectralObject.mapHomologicalFunctor_δ, homologySequenceδ,
          Triangulated.SpectralObject.triangle_mor₃, whiskerRight_app, ← shiftMap_comp,
          ← shiftMap_comp', Triangulated.SpectralObject.Hom.comm] }

@[simp]
lemma mapHomologicalSpectralObject_map_hom (F : C ⥤ A) [F.IsHomological]
    [F.ShiftSequence ℤ] (ι : Type*) [Category* ι] {X Y : Triangulated.SpectralObject C ι}
    (α : X ⟶ Y) (n : ℤ) :
    ((F.mapHomologicalSpectralObject ι).map α).hom n =
      Functor.whiskerRight α.hom (F.shift n) := rfl

section NatTrans

variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A natural transformation `τ : F₁ ⟶ F₂` between triangulated functors which commutes with the
shifts induces a natural transformation between the functors induced on spectral objects. -/
@[simps]
def _root_.CategoryTheory.NatTrans.mapTriangulatedSpectralObject {F₁ F₂ : C ⥤ D}
    [F₁.CommShift ℤ] [F₁.IsTriangulated] [F₂.CommShift ℤ] [F₂.IsTriangulated] (τ : F₁ ⟶ F₂)
    [NatTrans.CommShift τ ℤ] (ι : Type*) [Category* ι] :
    F₁.mapTriangulatedSpectralObject ι ⟶ F₂.mapTriangulatedSpectralObject ι where
  app X :=
    { hom := Functor.whiskerLeft X.ω₁ τ
      comm f g := by
        change (F₁.map (X.δ f g) ≫ (F₁.commShiftIso (1 : ℤ)).hom.app _) ≫ _ =
          _ ≫ F₂.map (X.δ f g) ≫ (F₂.commShiftIso (1 : ℤ)).hom.app _
        simp only [Category.assoc, NatTrans.shift_app_comm, NatTrans.naturality_assoc,
          Functor.whiskerLeft_app] }
  naturality X Y α := by
    ext1
    ext D
    simp only [Triangulated.SpectralObject.comp_hom, NatTrans.comp_app]
    change F₁.map (α.hom.app D) ≫ τ.app _ = τ.app _ ≫ F₂.map (α.hom.app D)
    exact τ.naturality (α.hom.app D)

variable {E : Type*} [Category* E] [HasZeroObject E] [Preadditive E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-- The functor induced on spectral objects by a composition of triangulated functors is the
composition of the induced functors. -/
def mapTriangulatedSpectralObjectCompIso (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] [G.CommShift ℤ] [G.IsTriangulated] (ι : Type*) [Category* ι] :
    (F ⋙ G).mapTriangulatedSpectralObject ι ≅
      F.mapTriangulatedSpectralObject ι ⋙ G.mapTriangulatedSpectralObject ι :=
  NatIso.ofComponents (fun X ↦
    { hom :=
        { hom := 𝟙 _
          comm f g := by
            change ((F ⋙ G).map (X.δ f g) ≫ ((F ⋙ G).commShiftIso (1 : ℤ)).hom.app _) ≫
                (shiftFunctor E (1 : ℤ)).map (𝟙 _) =
              𝟙 _ ≫ (G.map (F.map (X.δ f g) ≫ (F.commShiftIso (1 : ℤ)).hom.app _) ≫
                (G.commShiftIso (1 : ℤ)).hom.app _)
            simp [Functor.commShiftIso_comp_hom_app] }
      inv :=
        { hom := 𝟙 _
          comm f g := by
            change (G.map (F.map (X.δ f g) ≫ (F.commShiftIso (1 : ℤ)).hom.app _) ≫
                (G.commShiftIso (1 : ℤ)).hom.app _) ≫ (shiftFunctor E (1 : ℤ)).map (𝟙 _) =
              𝟙 _ ≫ ((F ⋙ G).map (X.δ f g) ≫ ((F ⋙ G).commShiftIso (1 : ℤ)).hom.app _)
            simp [Functor.commShiftIso_comp_hom_app] }
      hom_inv_id := by ext1; exact Category.comp_id _
      inv_hom_id := by ext1; exact Category.comp_id _ }) (fun α ↦ by
    ext1
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

@[simp]
lemma mapTriangulatedSpectralObjectCompIso_hom_app_hom (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] [G.CommShift ℤ] [G.IsTriangulated] (ι : Type*) [Category* ι]
    (X : Triangulated.SpectralObject C ι) :
    ((mapTriangulatedSpectralObjectCompIso F G ι).hom.app X).hom = 𝟙 _ := rfl

@[simp]
lemma mapTriangulatedSpectralObjectCompIso_inv_app_hom (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] [G.CommShift ℤ] [G.IsTriangulated] (ι : Type*) [Category* ι]
    (X : Triangulated.SpectralObject C ι) :
    ((mapTriangulatedSpectralObjectCompIso F G ι).inv.app X).hom = 𝟙 _ := rfl

end NatTrans

section Exact

variable {D A' : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Category* A'] [Abelian A']
  (H : C ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
  (H' : D ⥤ A') [H'.IsHomological] [H'.ShiftSequence ℤ]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (γ : A ⥤ A') [γ.Additive] [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
  (e : ∀ n : ℤ, H.shift n ⋙ γ ≅ F ⋙ H'.shift n)
  (he : ∀ (a a' : ℤ) (h : 1 + a = a') (X : C),
    γ.map ((H.shiftIso 1 a a' h).hom.app X) ≫ (e a').hom.app X =
      (e a).hom.app (X⟦(1 : ℤ)⟧) ≫ (H'.shift a).map ((F.commShiftIso (1 : ℤ)).hom.app X) ≫
        (H'.shiftIso 1 a a' h).hom.app (F.obj X))

/-- Let `H : C ⥤ A` and `H' : D ⥤ A'` be homological functors with shift sequences, `F : C ⥤ D`
a triangulated functor and `γ : A ⥤ A'` an exact functor, together with isomorphisms
`e n : H.shift n ⋙ γ ≅ F ⋙ H'.shift n` compatible with the shifts by `1`. Then applying `H` and
then `γ` to a spectral object gives the same spectral object as applying `F` and then `H'`. -/
noncomputable def mapHomologicalSpectralObjectCompMapSpectralObjectIso
    (ι : Type*) [Category* ι] :
    H.mapHomologicalSpectralObject ι ⋙ γ.mapSpectralObject ι ≅
      F.mapTriangulatedSpectralObject ι ⋙ H'.mapHomologicalSpectralObject ι :=
  NatIso.ofComponents (fun X ↦ Abelian.SpectralObject.isoMk
    (fun n ↦ Functor.isoWhiskerLeft X.ω₁ (e n)) (fun n₀ n₁ hn₁ i j k f g ↦ by
      change γ.map (H.shiftMap (X.δ f g) n₀ n₁ _) ≫ (e n₁).hom.app _ =
        (e n₀).hom.app _ ≫ H'.shiftMap (F.map (X.δ f g) ≫ (F.commShiftIso (1 : ℤ)).hom.app _)
          n₀ n₁ _
      simp only [shiftMap, Functor.map_comp, Category.assoc]
      rw [he n₀ n₁ (by lia)]
      exact ((e n₀).hom.naturality_assoc (X.δ f g) _).trans (by simp [Functor.comp_map])))
    (fun {X Y} α ↦ by
      refine Abelian.SpectralObject.Hom.ext (funext fun n ↦ ?_)
      ext D
      exact (e n).hom.naturality (α.hom.app D))

end Exact

end Functor

end CategoryTheory
