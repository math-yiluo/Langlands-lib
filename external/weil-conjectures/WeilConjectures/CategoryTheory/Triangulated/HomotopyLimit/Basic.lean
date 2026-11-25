/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Pro-isomorphisms of towers and homotopy limits

Let `F : ℕᵒᵖ ⥤ C` be a tower in a pretriangulated category. This file develops the homotopy
limit cones of `CategoryTheory.Pretriangulated.IsHomotopyLimit`, characterised by the Milnor
triangle `R lim F ⟶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ⟶ (R lim F)⟦1⟧`.

## Main results

- `CategoryTheory.Pretriangulated.isIso_of_proIso`: a morphism of Milnor triangles induced by a
  morphism of towers `a : F ⟶ G` which is a pro-isomorphism (it has an inverse up to a shift of
  the index) is an isomorphism on the homotopy limits, whatever the choice of the map between
  the homotopy limits. This is the triangulated form of the fact that a pro-isomorphism of towers
  induces isomorphisms on `lim` and `lim¹` (Stacks, Tag 0H9J).
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.hom_ext_zero`: maps from `L` to a homotopy
  limit vanish when all maps from `L` and `L⟦1⟧` to the terms of the tower do.

-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section TowerShift

variable {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[reassoc (attr := simp)]
lemma towerShift_proj (n : ℕ) :
    towerShift hP ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op :=
  Fan.IsLimit.fac hP _ n

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The maps from a cone to the product are fixed by the transition endomorphism. -/
@[reassoc (attr := simp)]
lemma lift_comp_towerShift (c : Cone F) :
    Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ towerShift hP =
      Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) :=
  Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [c.w]

end TowerShift

section ProIso

variable {F G : ℕᵒᵖ ⥤ C} {PF : Fan fun n : ℕ ↦ F.obj (op n)} (hPF : IsLimit PF)
  {PG : Fan fun n : ℕ ↦ G.obj (op n)} (hPG : IsLimit PG)

/-- The map `∏ₙ Fₙ ⟶ ∏ₙ Gₙ` induced by a morphism of towers. -/
noncomputable def productTowerMap (a : F ⟶ G) : PF.pt ⟶ PG.pt :=
  Fan.IsLimit.lift hPG fun n ↦ PF.proj n ≫ a.app (op n)

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[reassoc (attr := simp)]
lemma productTowerMap_proj (a : F ⟶ G) (n : ℕ) :
    productTowerMap (PF := PF) hPG a ≫ PG.proj n = PF.proj n ≫ a.app (op n) :=
  Fan.IsLimit.fac hPG _ n

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[reassoc]
lemma productTowerMap_comp_towerShift (a : F ⟶ G) :
    productTowerMap (PF := PF) hPG a ≫ towerShift hPG =
      towerShift hPF ≫ productTowerMap (PF := PF) hPG a :=
  Fan.IsLimit.hom_ext hPG _ _ fun n ↦ by
    simp only [assoc, towerShift_proj, productTowerMap_proj_assoc, productTowerMap_proj]
    rw [← a.naturality, towerShift_proj_assoc]

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
@[reassoc]
lemma productTowerMap_comp_sub_towerShift (a : F ⟶ G) :
    productTowerMap (PF := PF) hPG a ≫ (𝟙 _ - towerShift hPG) =
      (𝟙 _ - towerShift hPF) ≫ productTowerMap (PF := PF) hPG a := by
  rw [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp,
    productTowerMap_comp_towerShift]

/-- A morphism of towers `a : F ⟶ G` with an inverse `b` up to a shift of the index by one
(a *pro-isomorphism*) induces isomorphisms between the homotopy limits: if the triangles
`X ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ X⟦1⟧` and `Y ⟶ ∏ Gₙ ⟶ ∏ Gₙ ⟶ Y⟦1⟧` are Milnor triangles and `u : X ⟶ Y`
is part of the morphism of triangles induced by `a`, then `u` is an isomorphism. -/
theorem isIso_of_proIso {X Y : C} {cX : X ⟶ PF.pt} {δX : PF.pt ⟶ X⟦(1 : ℤ)⟧} {cY : Y ⟶ PG.pt}
    {δY : PG.pt ⟶ Y⟦(1 : ℤ)⟧} (hX : Triangle.mk cX (𝟙 _ - towerShift hPF) δX ∈ distTriang C)
    (hY : Triangle.mk cY (𝟙 _ - towerShift hPG) δY ∈ distTriang C) (a : F ⟶ G)
    (b : ∀ n : ℕ, G.obj (op (n + 1)) ⟶ F.obj (op n))
    (hb₁ : ∀ n, b n ≫ a.app (op n) = G.map (homOfLE n.le_succ).op)
    (hb₂ : ∀ n, a.app (op (n + 1)) ≫ b n = F.map (homOfLE n.le_succ).op)
    (u : X ⟶ Y) (hu₁ : cX ≫ productTowerMap (PF := PF) hPG a = u ≫ cY)
    (hu₃ : δX ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PF) hPG a ≫ δY) : IsIso u := by
  let c : PG.pt ⟶ PF.pt := Fan.IsLimit.lift hPF fun n ↦ PG.proj (n + 1) ≫ b n
  have hc (n : ℕ) : c ≫ PF.proj n = PG.proj (n + 1) ≫ b n := Fan.IsLimit.fac hPF _ n
  have hac : productTowerMap (PF := PF) hPG a ≫ c = towerShift hPF :=
    Fan.IsLimit.hom_ext hPF _ _ fun n ↦ by simp [hc, hb₂]
  have hca : c ≫ productTowerMap (PF := PF) hPG a = towerShift hPG :=
    Fan.IsLimit.hom_ext hPG _ _ fun n ↦ by simp [reassoc_of% hc, hb₁]
  have hcomm : (𝟙 _ - towerShift hPG) ≫ c = c ≫ (𝟙 _ - towerShift hPF) := by
    refine Fan.IsLimit.hom_ext hPF _ _ fun n ↦ ?_
    have : b (n + 1) ≫ F.map (homOfLE n.le_succ).op =
        G.map (homOfLE (n + 1).le_succ).op ≫ b n := by
      rw [← hb₂, reassoc_of% hb₁]
    rw [Preadditive.sub_comp, Preadditive.sub_comp, id_comp, assoc, hc, towerShift_proj_assoc,
      Preadditive.comp_sub, comp_id, Preadditive.sub_comp, assoc, towerShift_proj,
      reassoc_of% hc, this, hc]
  let φ : Triangle.mk cX (𝟙 _ - towerShift hPF) δX ⟶
      Triangle.mk cY (𝟙 _ - towerShift hPG) δY :=
    { hom₁ := u
      hom₂ := productTowerMap (PF := PF) hPG a
      hom₃ := productTowerMap (PF := PF) hPG a
      comm₁ := hu₁
      comm₂ := productTowerMap_comp_sub_towerShift hPF hPG a |>.symm
      comm₃ := hu₃ }
  obtain ⟨v, hv₁, hv₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hY hX c c hcomm
  let φ' : Triangle.mk cY (𝟙 _ - towerShift hPG) δY ⟶
      Triangle.mk cX (𝟙 _ - towerShift hPF) δX :=
    { hom₁ := v
      hom₂ := c
      hom₃ := c
      comm₁ := hv₁
      comm₂ := hcomm
      comm₃ := hv₃ }
  have hX₁ : cX ≫ towerShift hPF = cX := by
    have : cX ≫ (𝟙 _ - towerShift hPF) = 0 := comp_distTriang_mor_zero₁₂ _ hX
    rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at this
    exact this.symm
  have hX₃ : towerShift hPF ≫ δX = δX := by
    have : (𝟙 _ - towerShift hPF) ≫ δX = 0 := comp_distTriang_mor_zero₂₃ _ hX
    rw [Preadditive.sub_comp, id_comp, sub_eq_zero] at this
    exact this.symm
  have hY₁ : cY ≫ towerShift hPG = cY := by
    have : cY ≫ (𝟙 _ - towerShift hPG) = 0 := comp_distTriang_mor_zero₁₂ _ hY
    rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at this
    exact this.symm
  have hY₃ : towerShift hPG ≫ δY = δY := by
    have : (𝟙 _ - towerShift hPG) ≫ δY = 0 := comp_distTriang_mor_zero₂₃ _ hY
    rw [Preadditive.sub_comp, id_comp, sub_eq_zero] at this
    exact this.symm
  exact isIso_hom₁_of_comp hX hY φ φ'
    (by change cX ≫ _ ≫ c = cX; rw [hac, hX₁])
    (by change _ ≫ c ≫ δX = δX; rw [reassoc_of% hac, hX₃])
    (by change cY ≫ c ≫ _ = cY; rw [hca, hY₁])
    (by change c ≫ _ ≫ δY = δY; rw [reassoc_of% hca, hY₃])

end ProIso

/-- A map `L ⟶ R lim F` vanishes if all maps `L ⟶ Fₙ` and `L⟦1⟧ ⟶ Fₙ` vanish. -/
lemma IsHomotopyLimit.hom_ext_zero {F : ℕᵒᵖ ⥤ C} {c : Cone F} (hc : IsHomotopyLimit c) {L : C}
    (h₀ : ∀ (n : ℕ) (g : L ⟶ F.obj (op n)), g = 0)
    (h₁ : ∀ (n : ℕ) (g : L⟦(1 : ℤ)⟧ ⟶ F.obj (op n)), g = 0) (f : L ⟶ c.pt) : f = 0 := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hT (f⟦(1 : ℤ)⟧') (by
    have : f ≫ Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) = 0 :=
      Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [h₀ n (f ≫ c.π.app (op n))]
    change f⟦(1 : ℤ)⟧' ≫ (Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)))⟦(1 : ℤ)⟧' = 0
    rw [← Functor.map_comp, this, Functor.map_zero])
  have : g = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [h₁ n (g ≫ P.proj n)]
  rw [this, zero_comp] at hg
  exact (shiftFunctor C (1 : ℤ)).map_eq_zero_iff.mp hg

/-- Homotopy limits of towers exist as soon as a product `∏ₙ Fₙ` does: complete
`1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` to a distinguished triangle `L ⟶ ∏ₙ Fₙ ⟶ ∏ₙ Fₙ ⟶ L⟦1⟧`; the first map
is fixed by `t`, so its components form a cone over `F`, which is a homotopy limit cone by
construction. -/
lemma exists_isHomotopyLimit_of_isLimit {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) : ∃ c : Cone F, IsHomotopyLimit c := by
  obtain ⟨L, f, δ, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  have hf : f ≫ towerShift hP = f := by
    have h0 : f ≫ (𝟙 P.pt - towerShift hP) = 0 := comp_distTriang_mor_zero₁₂ _ hT
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h0
    exact h0.symm
  let c : Cone F :=
    { pt := L
      π := NatTrans.ofOpSequence (fun n ↦ f ≫ P.proj n) (fun n ↦ by
        dsimp
        rw [Category.id_comp, Category.assoc, ← towerShift_proj hP n, ← Category.assoc, hf]) }
  refine ⟨c, P, hP, δ, ?_⟩
  have hlift : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) = f :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [Fan.IsLimit.fac]
      simp [c, NatTrans.ofOpSequence_app]
  rw [hlift]
  exact hT

/-- Homotopy limits of towers exist in a pretriangulated category with countable products. -/
lemma exists_isHomotopyLimit (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)] :
    ∃ c : Cone F, IsHomotopyLimit c :=
  exists_isHomotopyLimit_of_isLimit (productIsProduct fun n : ℕ ↦ F.obj (op n))

end CategoryTheory.Pretriangulated
