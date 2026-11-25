/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Existence of homotopy limits and levelwise isomorphisms of towers

Let `F : ℕᵒᵖ ⥤ C` be a tower in a pretriangulated category `C` with countable products. This
file shows that `F` has a homotopy limit cone
(`CategoryTheory.Pretriangulated.exists_isHomotopyLimit`): complete `1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` to a
distinguished triangle `X ⟶ ∏ₙ Fₙ ⟶ ∏ₙ Fₙ ⟶ X⟦1⟧`; the components of the first map are
compatible with the transition maps because the first map is killed by `1 - t`.

It also records that a morphism of towers which is an isomorphism at every level induces an
isomorphism on homotopy limits, whatever the choice of the map completing the morphism of Milnor
triangles (`CategoryTheory.Pretriangulated.isIso_of_isIso_app`); the corresponding statement
for homotopy limit cones is `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_of_iso`.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The cone over a tower `F` whose legs are the components of a map `c : X ⟶ ∏ₙ Fₙ` fixed by the
transition endomorphism `t` of the product. -/
noncomputable def coneOfComp {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)
    {X : C} (c : X ⟶ P.pt) (hc : c ≫ towerShift hP = c) : Cone F where
  pt := X
  π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj X) (fun n ↦ c ≫ P.proj n)
    (fun n ↦ by
      dsimp
      rw [id_comp, assoc, ← towerShift_proj hP, ← assoc, hc])

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[simp]
lemma coneOfComp_π_app {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)
    {X : C} (c : X ⟶ P.pt) (hc : c ≫ towerShift hP = c) (n : ℕ) :
    (coneOfComp hP c hc).π.app (op n) = c ≫ P.proj n :=
  rfl

/-- The first map `c : X ⟶ ∏ₙ Fₙ` of a Milnor triangle is fixed by the transition endomorphism
`t`, being killed by `1 - t`. -/
lemma comp_towerShift_of_distinguished {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) {X : C} {c : X ⟶ P.pt} {δ : P.pt ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk c (𝟙 _ - towerShift hP) δ ∈ distTriang C) : c ≫ towerShift hP = c := by
  have : c ≫ (𝟙 P.pt - towerShift hP) = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at this
  exact this.symm

/-- The cone over a tower `F` given by the first map `c : X ⟶ ∏ₙ Fₙ` of a Milnor triangle
`X ⟶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ⟶ X⟦1⟧` is a homotopy limit cone. -/
lemma isHomotopyLimit_coneOfComp {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) {X : C} {c : X ⟶ P.pt} {δ : P.pt ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk c (𝟙 _ - towerShift hP) δ ∈ distTriang C) :
    IsHomotopyLimit (coneOfComp hP c (comp_towerShift_of_distinguished hP hT)) := by
  refine ⟨P, hP, δ, ?_⟩
  have : Fan.IsLimit.lift hP (fun n ↦ (coneOfComp hP c
      (comp_towerShift_of_distinguished hP hT)).π.app (op n)) = c :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp
  rw [this]
  exact hT

/-- A morphism of towers `a : F ⟶ G` which is an isomorphism at every level induces an
isomorphism on homotopy limits: if `X ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ X⟦1⟧` and `Y ⟶ ∏ Gₙ ⟶ ∏ Gₙ ⟶ Y⟦1⟧` are
Milnor triangles and `u : X ⟶ Y` completes the morphism of triangles induced by `a`, then `u` is
an isomorphism. -/
theorem isIso_of_isIso_app {F G : ℕᵒᵖ ⥤ C} {PF : Fan fun n : ℕ ↦ F.obj (op n)}
    (hPF : IsLimit PF) {PG : Fan fun n : ℕ ↦ G.obj (op n)} (hPG : IsLimit PG) {X Y : C}
    {cX : X ⟶ PF.pt} {δX : PF.pt ⟶ X⟦(1 : ℤ)⟧} {cY : Y ⟶ PG.pt} {δY : PG.pt ⟶ Y⟦(1 : ℤ)⟧}
    (hX : Triangle.mk cX (𝟙 _ - towerShift hPF) δX ∈ distTriang C)
    (hY : Triangle.mk cY (𝟙 _ - towerShift hPG) δY ∈ distTriang C) (a : F ⟶ G)
    [∀ n, IsIso (a.app n)] (u : X ⟶ Y)
    (hu₁ : cX ≫ productTowerMap (PF := PF) hPG a = u ≫ cY)
    (hu₃ : δX ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PF) hPG a ≫ δY) : IsIso u :=
  isIso_of_proIso hPF hPG hX hY a (fun n ↦ G.map (homOfLE n.le_succ).op ≫ inv (a.app (op n)))
    (fun n ↦ by simp) (fun n ↦ by simp [← NatTrans.naturality_assoc]) u hu₁ hu₃

end CategoryTheory.Pretriangulated
