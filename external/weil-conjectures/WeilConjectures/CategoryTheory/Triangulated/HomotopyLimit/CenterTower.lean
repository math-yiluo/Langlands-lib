/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Center.Basic
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic

/-!
# Completeness with respect to a central endomorphism

Let `C` be a pretriangulated category and `z` an element of the center of `C`, that is a natural
endomorphism `z_X : X ⟶ X` of the identity functor (for instance the multiplication by a
uniformizer `ϖ` on a derived category of `𝒪_E`-modules). An object `K` is *`z`-complete* if every
morphism `Z ⟶ K` from an object `Z` on which `z` acts invertibly vanishes
(`CategoryTheory.Pretriangulated.IsCenterComplete`).

Write `T(K)` for the homotopy limit of the tower `⋯ --z--> K --z--> K`
(`CategoryTheory.Pretriangulated.centerTower`). We show that, when `z` commutes with the shift,
`K` is `z`-complete if and only if `T(K)` vanishes:

* `CategoryTheory.Pretriangulated.isCenterComplete_of_isHomotopyLimit_centerTower`: if `T(K) = 0`,
  then `K` is `z`-complete: for `f : Z ⟶ K` with `z_Z` invertible, the maps `z_Z^{-n} ≫ f` form
  a cone over the tower, which lifts to `Z ⟶ T(K) = 0`.
* `CategoryTheory.Pretriangulated.IsCenterComplete.isZero_of_isHomotopyLimit`: if `K` is
  `z`-complete, then `T(K) = 0`: `z` acts invertibly on `T(K)`, the tower being pro-isomorphic to
  itself through `z`, so all maps `T(K) ⟶ K` and `T(K)⟦1⟧ ⟶ K` vanish.

As a consequence, a triangulated functor which preserves the relevant countable products and
commutes with the central endomorphisms preserves complete objects
(`CategoryTheory.Pretriangulated.IsCenterComplete.map`).
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category* C]

/-- The tower `⋯ --z--> K --z--> K` of an object `K`, for an element `z` of the center. -/
noncomputable def centerTower (z : CatCenter C) (K : C) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun _ ↦ K) fun _ ↦ z.app K

@[simp]
lemma centerTower_obj (z : CatCenter C) (K : C) (n : ℕᵒᵖ) : (centerTower z K).obj n = K := rfl

@[simp]
lemma centerTower_map_succ (z : CatCenter C) (K : C) (n : ℕ) :
    (centerTower z K).map (homOfLE (Nat.le_add_right n 1)).op = z.app K :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

variable [Preadditive C]

/-- An object `K` is *complete* with respect to an element `z` of the center if every morphism to
`K` from an object on which `z` acts invertibly vanishes. -/
def IsCenterComplete (z : CatCenter C) (K : C) : Prop :=
  ∀ ⦃Z : C⦄, IsIso (z.app Z) → ∀ f : Z ⟶ K, f = 0

/-- Complete objects are closed under isomorphisms. -/
lemma IsCenterComplete.of_iso {z : CatCenter C} {K K' : C} (hK : IsCenterComplete z K)
    (e : K ≅ K') : IsCenterComplete z K' := by
  intro Z hZ f
  rw [← cancel_mono e.inv, hK hZ (f ≫ e.inv), zero_comp]

/-- The legs `z_Z^{-n} ≫ f` of the cone over `⋯ --z--> K --z--> K` induced by a morphism
`f : Z ⟶ K` from an object on which `z` acts invertibly. -/
noncomputable def centerTowerConeLeg (z : CatCenter C) {Z K : C} [IsIso (z.app Z)] (f : Z ⟶ K) :
    ℕ → (Z ⟶ K)
  | 0 => f
  | n + 1 => inv (z.app Z) ≫ centerTowerConeLeg z f n

omit [Preadditive C] in
/-- The legs `z_Z^{-n} ≫ f` are compatible with the transition maps `z_K`. -/
lemma centerTowerConeLeg_succ_comp (z : CatCenter C) {Z K : C} [IsIso (z.app Z)] (f : Z ⟶ K)
    (n : ℕ) : centerTowerConeLeg z f (n + 1) ≫ z.app K = centerTowerConeLeg z f n := by
  rw [centerTowerConeLeg, assoc, z.naturality, IsIso.inv_hom_id_assoc]

/-- The cone over `⋯ --z--> K --z--> K` with legs `z_Z^{-n} ≫ f`, for `f : Z ⟶ K` and `z_Z`
invertible. -/
noncomputable def centerTowerCone (z : CatCenter C) {Z K : C} [IsIso (z.app Z)] (f : Z ⟶ K) :
    Cone (centerTower z K) where
  pt := Z
  π := NatTrans.ofOpSequence (fun n ↦ centerTowerConeLeg (Z := Z) (K := K) z f n) fun n ↦ by
    rw [centerTower_map_succ]
    exact (id_comp _).trans (centerTowerConeLeg_succ_comp z f n).symm

omit [Preadditive C] in
@[simp]
lemma centerTowerCone_π_app_zero (z : CatCenter C) {Z K : C} [IsIso (z.app Z)] (f : Z ⟶ K) :
    (centerTowerCone z f).π.app (op 0) = f :=
  rfl

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Every cone over a homotopy limit cone factors through it (not uniquely). -/
lemma IsHomotopyLimit.exists_lift {F : ℕᵒᵖ ⥤ C} {c : Cone F} (hc : IsHomotopyLimit c)
    (s : Cone F) : ∃ l : s.pt ⟶ c.pt, ∀ n : ℕ, l ≫ c.π.app (op n) = s.π.app (op n) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  have h₀ : (Fan.IsLimit.lift hP fun n ↦ s.π.app (op n)) ≫ (𝟙 P.pt - towerShift hP) = 0 := by
    rw [Preadditive.comp_sub, comp_id, lift_comp_towerShift hP s, sub_self]
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₂ _ hT _ h₀
  refine ⟨l, fun n ↦ ?_⟩
  have := hl =≫ P.proj n
  simp only [Fan.IsLimit.fac, Triangle.mk_mor₁, assoc] at this
  exact this.symm


/-- If the homotopy limit `T(K)` of `⋯ --z--> K --z--> K` vanishes, then `K` is complete. -/
lemma isCenterComplete_of_isHomotopyLimit_centerTower {z : CatCenter C} {K : C}
    {c : Cone (centerTower z K)} (hc : IsHomotopyLimit c) (h : IsZero c.pt) :
    IsCenterComplete z K := by
  intro Z _ f
  obtain ⟨l, hl⟩ := hc.exists_lift (centerTowerCone z f)
  have := hl 0
  rw [h.eq_of_tgt l 0, zero_comp, centerTowerCone_π_app_zero] at this
  exact this.symm

/-- If `K` is complete with respect to an element `z` of the center commuting with the shift by
`1`, the homotopy limit `T(K)` of `⋯ --z--> K --z--> K` vanishes. -/
lemma IsCenterComplete.isZero_of_isHomotopyLimit {z : CatCenter C}
    (hz : ∀ X : C, z.app (X⟦(1 : ℤ)⟧) = (z.app X)⟦(1 : ℤ)⟧') {K : C}
    (hK : IsCenterComplete z K) {c : Cone (centerTower z K)} (hc : IsHomotopyLimit c) :
    IsZero c.pt := by
  have hiso : IsIso (z.app c.pt) := by
    obtain ⟨P, hP, δ, hT⟩ := hc
    let a : centerTower z K ⟶ centerTower z K :=
      { app n := z.app _
        naturality _ _ g := z.naturality ((centerTower z K).map g) }
    have ha : productTowerMap (PF := P) hP a = z.app P.pt :=
      Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
        rw [productTowerMap_proj]
        exact z.naturality _
    refine isIso_of_proIso hP hP hT hT a (fun _ ↦ 𝟙 K) (fun n ↦ ?_) (fun n ↦ ?_) (z.app c.pt)
      ?_ ?_
    · rw [centerTower_map_succ]
      exact id_comp _
    · rw [centerTower_map_succ]
      exact comp_id _
    · rw [ha]
      exact z.naturality _
    · rw [ha, ← hz]
      exact z.naturality _
  have hiso₁ : IsIso (z.app (c.pt⟦(1 : ℤ)⟧)) := by
    rw [hz]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  exact hc.hom_ext_zero (fun _ g ↦ hK hiso g) (fun _ g ↦ hK hiso₁ g) _

section Map

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The image of the tower `⋯ --z--> K --z--> K` under a functor commuting with the central
endomorphisms is the tower `⋯ --z'--> Φ K --z'--> Φ K`. -/
noncomputable def centerTowerCompIso (z : CatCenter C) (z' : CatCenter D) (Φ : C ⥤ D)
    (hΦ : ∀ X : C, Φ.map (z.app X) = z'.app (Φ.obj X)) (K : C) :
    centerTower z K ⋙ Φ ≅ centerTower z' (Φ.obj K) where
  hom := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) fun n ↦ by
    rw [Functor.comp_map, centerTower_map_succ, centerTower_map_succ]
    exact (comp_id _).trans ((hΦ K).trans (id_comp _).symm)
  inv := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) fun n ↦ by
    rw [Functor.comp_map, centerTower_map_succ, centerTower_map_succ]
    exact (comp_id _).trans ((hΦ K).symm.trans (id_comp _).symm)
  hom_inv_id := by
    ext
    exact id_comp _
  inv_hom_id := by
    ext
    exact id_comp _

/-- A triangulated functor which commutes with the central endomorphisms and preserves the
countable power `∏ₙ K` sends a complete object `K` to a complete object, provided the central
endomorphism commutes with the shift by `1` and the power `∏ₙ K` exists. -/
lemma IsCenterComplete.map {z : CatCenter C} (z' : CatCenter D)
    (hz : ∀ X : C, z.app (X⟦(1 : ℤ)⟧) = (z.app X)⟦(1 : ℤ)⟧') (Φ : C ⥤ D) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Additive] (hΦ : ∀ X : C, Φ.map (z.app X) = z'.app (Φ.obj X))
    {K : C} [HasProduct fun _ : ℕ ↦ K] [PreservesLimit (Discrete.functor fun _ : ℕ ↦ K) Φ]
    (hK : IsCenterComplete z K) : IsCenterComplete z' (Φ.obj K) := by
  have : HasProduct fun n : ℕ ↦ (centerTower z K).obj (op n) := by
    dsimp
    infer_instance
  obtain ⟨c, hc⟩ := exists_isHomotopyLimit (centerTower z K)
  have : PreservesLimit (Discrete.functor fun n : ℕ ↦ (centerTower z K).obj (op n)) Φ := by
    dsimp
    infer_instance
  have hc' := (hc.map Φ).of_iso (centerTowerCompIso z z' Φ hΦ K)
    { pt := Φ.obj c.pt
      π := (Φ.mapCone c).π ≫ (centerTowerCompIso z z' Φ hΦ K).hom } (Iso.refl _)
    fun n ↦ by simp
  exact isCenterComplete_of_isHomotopyLimit_centerTower hc'
    (Φ.map_isZero (hK.isZero_of_isHomotopyLimit hz hc))

end Map

end CategoryTheory.Pretriangulated
