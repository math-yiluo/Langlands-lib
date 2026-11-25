/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Homotopy limits of towers of triangles

Let `F ⟶ G ⟶ H ⟶ F⟦1⟧` be a tower (indexed by `ℕᵒᵖ`) of distinguished triangles in a
pretriangulated category with countable products, whose third term is a constant object `H`
and whose first term `F` is *pro-zero*: the composite of `N` consecutive transition maps of `F`
vanishes. Then the map `R lim G ⟶ H` induced by `G ⟶ H` is an isomorphism. This is the
triangulated form of the fact that the derived limit of a pro-zero tower vanishes.

## Main results

- `CategoryTheory.Pretriangulated.isIso_of_endo_triangle`: let `φ` be an endomorphism of a
  distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` such that `φ.hom₁` is an isomorphism and
  `φ.hom₃` has a section. Then the map from a fiber of `φ.hom₂` to a fiber of `φ.hom₃` induced
  by `T.mor₂` is an isomorphism.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.isIso_π_comp_of_triangles`: the statement
  above about towers of triangles.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.whiskerAdd`: the legs `c.π (n + k)` of a
  homotopy limit cone exhibit its point as the homotopy limit of the shifted tower
  `n ↦ F (n + k)`.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_of_iso`: isomorphic towers have
  isomorphic homotopy limits, compatibly with the legs.

-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Let `φ : T ⟶ T` be an endomorphism of a distinguished triangle such that `φ.hom₁` is an
isomorphism and `φ.hom₃` has a section `σ`. If `X` and `Y` are fibers of `φ.hom₂` and `φ.hom₃`
(the first objects of distinguished triangles `X ⟶ T.obj₂ ⟶ T.obj₂ ⟶ X⟦1⟧` and
`Y ⟶ T.obj₃ ⟶ T.obj₃ ⟶ Y⟦1⟧` with second maps `φ.hom₂` and `φ.hom₃`), then every map
`u : X ⟶ Y` compatible with `T.mor₂` is an isomorphism. -/
theorem isIso_of_endo_triangle (T : Triangle C) (hT : T ∈ distTriang C) (φ : T ⟶ T)
    [IsIso φ.hom₁] (σ : T.obj₃ ⟶ T.obj₃) (hσ : σ ≫ φ.hom₃ = 𝟙 _)
    {X Y : C} {ℓ : X ⟶ T.obj₂} {δ : T.obj₂ ⟶ X⟦(1 : ℤ)⟧}
    (hX : Triangle.mk ℓ φ.hom₂ δ ∈ distTriang C)
    {ℓ' : Y ⟶ T.obj₃} {δ' : T.obj₃ ⟶ Y⟦(1 : ℤ)⟧}
    (hY : Triangle.mk ℓ' φ.hom₃ δ' ∈ distTriang C)
    (u : X ⟶ Y) (hu : ℓ ≫ T.mor₂ = u ≫ ℓ') : IsIso u := by
  have hℓ'φ : ℓ' ≫ φ.hom₃ = 0 := comp_distTriang_mor_zero₁₂ _ hY
  have hℓφ : ℓ ≫ φ.hom₂ = 0 := comp_distTriang_mor_zero₁₂ _ hX
  have hδ' : δ' = 0 := by
    have : φ.hom₃ ≫ δ' = 0 := comp_distTriang_mor_zero₂₃ _ hY
    calc δ' = (σ ≫ φ.hom₃) ≫ δ' := by rw [hσ, id_comp]
      _ = 0 := by rw [assoc, this, comp_zero]
  have : Mono ℓ' := Triangle.mono₁ _ hY hδ'
  have hc : ℓ' ≫ T.mor₃ = 0 := by
    rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), zero_comp, assoc, φ.comm₃, reassoc_of% hℓ'φ,
      zero_comp]
  -- a left inverse of `φ.hom₂`, which forces `δ = 0`
  obtain ⟨x₀, hx₀⟩ := T.coyoneda_exact₃ hT (T.mor₂ ≫ σ) (by
    rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), zero_comp, assoc, assoc, φ.comm₃,
      reassoc_of% hσ, comp_distTriang_mor_zero₂₃ _ hT])
  obtain ⟨r, hr⟩ := T.coyoneda_exact₂ hT (x₀ ≫ φ.hom₂ - 𝟙 _) (by
    rw [Preadditive.sub_comp, assoc, ← φ.comm₂, ← reassoc_of% hx₀, hσ, comp_id, id_comp,
      sub_self])
  have hx : (x₀ - r ≫ inv φ.hom₁ ≫ T.mor₁) ≫ φ.hom₂ = 𝟙 _ := by
    rw [Preadditive.sub_comp, assoc, assoc, φ.comm₁, IsIso.inv_hom_id_assoc, ← hr,
      sub_sub_cancel]
  have hδ : δ = 0 := by
    have : φ.hom₂ ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ hX
    calc δ = ((x₀ - r ≫ inv φ.hom₁ ≫ T.mor₁) ≫ φ.hom₂) ≫ δ := by rw [hx, id_comp]
      _ = 0 := by rw [assoc, this, comp_zero]
  have : Mono ℓ := Triangle.mono₁ _ hX hδ
  -- maps to `T.obj₂` killed by `T.mor₂` and by `φ.hom₂` vanish
  have hZ : ∀ {W : C} (d : W ⟶ T.obj₂), d ≫ T.mor₂ = 0 → d ≫ φ.hom₂ = 0 → d = 0 := by
    intro W d hd₁ hd₂
    obtain ⟨s, rfl⟩ := T.coyoneda_exact₂ hT d hd₁
    let ψ := (invRotate C).map φ
    obtain ⟨p, hp⟩ := T.invRotate.coyoneda_exact₂ (inv_rot_of_distTriang _ hT) (s ≫ φ.hom₁)
      (by
        change (s ≫ φ.hom₁) ≫ T.mor₁ = 0
        rw [assoc, ← φ.comm₁, ← assoc, hd₂])
    have key : T.invRotate.mor₁ ≫ inv φ.hom₁ = σ⟦(-1 : ℤ)⟧' ≫ T.invRotate.mor₁ := by
      rw [IsIso.comp_inv_eq, assoc]
      have h₁ : T.invRotate.mor₁ ≫ φ.hom₁ = φ.hom₃⟦(-1 : ℤ)⟧' ≫ T.invRotate.mor₁ := ψ.comm₁
      rw [h₁, ← Functor.map_comp_assoc, hσ, CategoryTheory.Functor.map_id, id_comp]
    have hs : s = p ≫ σ⟦(-1 : ℤ)⟧' ≫ T.invRotate.mor₁ := by
      rw [← key, ← assoc, ← hp, assoc, IsIso.hom_inv_id, comp_id]
    rw [hs, assoc, assoc]
    change p ≫ σ⟦(-1 : ℤ)⟧' ≫ T.invRotate.mor₁ ≫ T.invRotate.mor₂ = 0
    rw [comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hT), comp_zero, comp_zero]
  -- a right inverse of `u`
  obtain ⟨y₀, hy₀⟩ := T.coyoneda_exact₃ hT ℓ' hc
  obtain ⟨w, hw⟩ := T.coyoneda_exact₂ hT (y₀ ≫ φ.hom₂) (by
    rw [assoc, ← φ.comm₂, ← reassoc_of% hy₀, hℓ'φ])
  have hy₂ : (y₀ - w ≫ inv φ.hom₁ ≫ T.mor₁) ≫ T.mor₂ = ℓ' := by
    rw [Preadditive.sub_comp, assoc, assoc, comp_distTriang_mor_zero₁₂ _ hT, comp_zero,
      comp_zero, sub_zero, hy₀]
  have hyφ : (y₀ - w ≫ inv φ.hom₁ ≫ T.mor₁) ≫ φ.hom₂ = 0 := by
    rw [Preadditive.sub_comp, assoc, assoc, φ.comm₁, IsIso.inv_hom_id_assoc, hw, sub_self]
  obtain ⟨v, hv⟩ := (Triangle.mk ℓ φ.hom₂ δ).coyoneda_exact₂ hX _ hyφ
  replace hv : y₀ - w ≫ inv φ.hom₁ ≫ T.mor₁ = v ≫ ℓ := hv
  have hvu : v ≫ u = 𝟙 Y := by
    rw [← cancel_mono ℓ', assoc, ← hu, ← assoc, ← hv, hy₂, id_comp]
  have huv : u ≫ v = 𝟙 X := by
    rw [← cancel_mono ℓ, id_comp]
    refine sub_eq_zero.1 (hZ _ ?_ ?_)
    · rw [Preadditive.sub_comp, assoc, assoc, ← assoc v ℓ, ← hv, hy₂, hu, sub_self]
    · rw [Preadditive.sub_comp, assoc, assoc, hℓφ, comp_zero, comp_zero, sub_self]
  exact ⟨v, huv, hvu⟩

section TowerShift

variable {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The `k`-th power of the transition endomorphism `t` of `∏ₙ Fₙ` has components
`∏ Fₙ ⟶ Fₙ₊ₖ ⟶ Fₙ`. -/
lemma towerShift_pow_proj (k n : ℕ) :
    ((End.of (towerShift hP) ^ k).asHom) ≫ P.proj n =
      P.proj (n + k) ≫ F.map (homOfLE (Nat.le_add_right n k)).op := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, End.one_asHom, id_comp]
    exact (Category.comp_id _).symm.trans (by congr 1; exact (F.map_id _).symm)
  | succ k ih =>
    rw [pow_succ, End.mul_asHom, assoc, ih, towerShift_proj_assoc, ← F.map_comp]
    rfl

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- If the composites of `N` consecutive transition maps of `F` vanish, then `𝟙 - t` is an
isomorphism of `∏ₙ Fₙ`. -/
lemma isIso_sub_towerShift_of_eq_zero (N : ℕ)
    (hN : ∀ n : ℕ, F.map (homOfLE (Nat.le_add_right n N)).op = 0) :
    IsIso (𝟙 P.pt - towerShift hP) := by
  have h : (End.of (towerShift hP) ^ N) = 0 := by
    apply End.ext
    exact Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [towerShift_pow_proj, hN, End.zero_asHom, comp_zero, zero_comp]
  have : IsUnit (1 - End.of (towerShift hP)) := IsNilpotent.isUnit_one_sub ⟨N, h⟩
  exact (isUnit_iff_isIso _).1 this

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- For a constant tower, `𝟙 - t` has a section. -/
lemma exists_comp_sub_towerShift_eq_id {H : C}
    {P : Fan fun _ : ℕ ↦ ((Functor.const ℕᵒᵖ).obj H).obj (op 0)} (hP : IsLimit P) :
    ∃ σ : P.pt ⟶ P.pt, σ ≫ (𝟙 P.pt - towerShift (F := (Functor.const ℕᵒᵖ).obj H) hP) =
      𝟙 _ := by
  refine ⟨Fan.IsLimit.lift hP fun n ↦ -∑ k ∈ Finset.range n, P.proj k,
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_⟩
  rw [Preadditive.comp_sub, comp_id, Preadditive.sub_comp, assoc, towerShift_proj,
    Fan.IsLimit.fac, ← assoc, Fan.IsLimit.fac, id_comp]
  dsimp
  rw [comp_id, Finset.sum_range_succ, neg_add_rev]
  abel

end TowerShift

namespace IsHomotopyLimit

/-- The Milnor triangle of a homotopy limit cone can be formed with any product of the tower. -/
lemma exists_distTriang {F : ℕᵒᵖ ⥤ C} {c : Cone F} (hc : IsHomotopyLimit c)
    {P' : Fan fun n : ℕ ↦ F.obj (op n)} (hP' : IsLimit P') :
    ∃ δ : P'.pt ⟶ c.pt⟦(1 : ℤ)⟧,
      Triangle.mk (Fan.IsLimit.lift hP' fun n ↦ c.π.app (op n)) (𝟙 _ - towerShift hP') δ ∈
        distTriang C := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let e : P.pt ≅ P'.pt := hP.conePointUniqueUpToIso hP'
  have he (n : ℕ) : e.hom ≫ P'.proj n = P.proj n :=
    hP.conePointUniqueUpToIso_hom_comp hP' ⟨n⟩
  have ht : towerShift hP ≫ e.hom = e.hom ≫ towerShift hP' :=
    Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
      rw [assoc, he, towerShift_proj, assoc, towerShift_proj, ← assoc, he]
  refine ⟨e.inv ≫ δ, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_)⟩
  · refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
    simp only [Triangle.mk_mor₁, Iso.refl_hom, id_comp,
      Iso.symm_hom, assoc, Fan.IsLimit.fac]
    rw [← he, e.inv_hom_id_assoc, Fan.IsLimit.fac]
  · have ht' : towerShift hP' ≫ e.inv = e.inv ≫ towerShift hP := by
      rw [← cancel_epi e.hom, ← reassoc_of% ht, e.hom_inv_id, comp_id, e.hom_inv_id_assoc]
    change (𝟙 _ - towerShift hP') ≫ e.inv = e.inv ≫ (𝟙 _ - towerShift hP)
    rw [Preadditive.sub_comp, Preadditive.comp_sub, ht', id_comp, comp_id]
  · simp

end IsHomotopyLimit

section Triangles

variable [HasLimitsOfShape (Discrete ℕ) C]

/-- Let `F ⟶ G ⟶ H ⟶ F⟦1⟧` be a tower of distinguished triangles whose third term is a
constant object `H` and whose first term is pro-zero: the composites of `N` consecutive
transition maps of `F` vanish. Then for every homotopy limit cone `c` of `G`, the induced map
`c.pt ⟶ H` is an isomorphism. -/
theorem IsHomotopyLimit.isIso_π_comp_of_triangles {F G : ℕᵒᵖ ⥤ C} {H : C} (ι : F ⟶ G)
    (β : G ⟶ (Functor.const ℕᵒᵖ).obj H)
    (δ : (Functor.const ℕᵒᵖ).obj H ⟶ F ⋙ shiftFunctor C (1 : ℤ))
    (hT : ∀ n : ℕ, Triangle.mk (ι.app (op n)) (β.app (op n)) (δ.app (op n)) ∈ distTriang C)
    (N : ℕ) (hN : ∀ n : ℕ, F.map (homOfLE (Nat.le_add_right n N)).op = 0)
    {c : Cone G} (hc : IsHomotopyLimit c) : IsIso (c.π.app (op 0) ≫ β.app (op 0)) := by
  let T : ℕ → Triangle C := fun n ↦ Triangle.mk (ι.app (op n)) (β.app (op n)) (δ.app (op n))
  have hPT : productTriangle T ∈ distTriang C := productTriangle_distinguished T hT
  let tr (n : ℕ) : T (n + 1) ⟶ T n :=
    Triangle.homMk _ _ (F.map (homOfLE n.le_succ).op) (G.map (homOfLE n.le_succ).op) (𝟙 H)
      (ι.naturality _).symm (β.naturality (homOfLE n.le_succ).op).symm
      (δ.naturality (homOfLE n.le_succ).op).symm
  let τ : productTriangle T ⟶ productTriangle T :=
    productTriangle.lift T fun n ↦ productTriangle.π T (n + 1) ≫ tr n
  let hPF : IsLimit (Fan.mk _ (Pi.π fun n ↦ F.obj (op n))) := productIsProduct _
  let hPG : IsLimit (Fan.mk _ (Pi.π fun n ↦ G.obj (op n))) := productIsProduct _
  let hPH : IsLimit (Fan.mk _ (Pi.π fun _ : ℕ ↦ ((Functor.const ℕᵒᵖ).obj H).obj (op 0))) :=
    productIsProduct _
  have hτ₁ : τ.hom₁ = towerShift (F := F) hPF :=
    Fan.IsLimit.hom_ext hPF _ _ fun n ↦ by
      rw [towerShift_proj]
      simp only [τ, tr, productTriangle.lift_hom₁, comp_hom₁, productTriangle.π_hom₁,
        Triangle.homMk_hom₁]
      exact Pi.lift_comp_π _ _
  have hτ₂ : τ.hom₂ = towerShift (F := G) hPG :=
    Fan.IsLimit.hom_ext hPG _ _ fun n ↦ by
      rw [towerShift_proj]
      simp only [τ, tr, productTriangle.lift_hom₂, comp_hom₂, productTriangle.π_hom₂,
        Triangle.homMk_hom₂]
      exact Pi.lift_comp_π _ _
  have hτ₃ : τ.hom₃ = towerShift (F := (Functor.const ℕᵒᵖ).obj H) hPH :=
    Fan.IsLimit.hom_ext hPH _ _ fun n ↦ by
      rw [towerShift_proj]
      simp only [τ, tr, productTriangle.lift_hom₃, comp_hom₃, productTriangle.π_hom₃,
        Triangle.homMk_hom₃]
      exact Pi.lift_comp_π _ _
  let φ : productTriangle T ⟶ productTriangle T :=
    Triangle.homMk _ _ (𝟙 _ - τ.hom₁) (𝟙 _ - τ.hom₂) (𝟙 _ - τ.hom₃)
      (by rw [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, τ.comm₁])
      (by rw [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, τ.comm₂])
      (by
        rw [Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.comp_sub,
          Preadditive.sub_comp, comp_id, id_comp, τ.comm₃])
  have : IsIso φ.hom₁ := by
    change IsIso (𝟙 _ - τ.hom₁)
    rw [hτ₁]
    exact isIso_sub_towerShift_of_eq_zero hPF N hN
  obtain ⟨σ, hσ⟩ := exists_comp_sub_towerShift_eq_id (H := H) hPH
  obtain ⟨δG, hG⟩ := hc.exists_distTriang hPG
  let cH : Cone ((Functor.const ℕᵒᵖ).obj H) := { pt := H, π := 𝟙 _ }
  have : ∀ n, IsIso (cH.π.app n) := fun n ↦ by dsimp [cH]; infer_instance
  obtain ⟨δH, hH⟩ := (IsHomotopyLimit.of_isIso_π cH).exists_distTriang hPH
  have hφ₂ : φ.hom₂ = 𝟙 _ - towerShift (F := G) hPG := by
    change 𝟙 _ - τ.hom₂ = _
    rw [hτ₂]
    rfl
  have hφ₃ : φ.hom₃ = 𝟙 _ - towerShift (F := (Functor.const ℕᵒᵖ).obj H) hPH := by
    change 𝟙 _ - τ.hom₃ = _
    rw [hτ₃]
    rfl
  refine isIso_of_endo_triangle _ hPT φ σ (by rw [hφ₃]; exact hσ) (by rw [hφ₂]; exact hG)
    (by rw [hφ₃]; exact hH) _ ?_
  refine Pi.hom_ext _ _ fun n ↦ ?_
  have h₁ := c.w (homOfLE (Nat.zero_le n)).op
  have h₂ := β.naturality (homOfLE (Nat.zero_le n)).op
  dsimp at h₂
  rw [comp_id] at h₂
  simp only [productTriangle_mor₂, assoc, Pi.map_π]
  erw [Fan.IsLimit.fac_assoc, Fan.IsLimit.fac]
  rw [← h₁, assoc, reassoc_of% h₂]
  simp [cH, T]

end Triangles

section Shift

/-- The functor `ℕᵒᵖ ⥤ ℕᵒᵖ` sending `n` to `n + k`. -/
def addOpFunctor (k : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (Monotone.functor (f := fun n : ℕ ↦ n + k) fun _ _ h ↦ Nat.add_le_add_right h k).op

@[simp]
lemma addOpFunctor_obj (k n : ℕ) : (addOpFunctor k).obj (op n) = op (n + k) := rfl

/-- The legs `c.π (n + k)` of a homotopy limit cone exhibit its point as the homotopy limit of
the shifted tower `n ↦ F (n + k)`: the projection `∏ₙ Fₙ ⟶ ∏ₙ Fₙ₊ₖ` and the map
`∏ₙ Fₙ₊ₖ ⟶ ∏ₙ Fₙ` with components `Fₙ₊ₖ ⟶ Fₙ` compose to `tᵏ` both ways. -/
lemma IsHomotopyLimit.whiskerAdd [HasLimitsOfShape (Discrete ℕ) C] {F : ℕᵒᵖ ⥤ C} {c : Cone F}
    (hc : IsHomotopyLimit c) (k : ℕ) : IsHomotopyLimit (c.whisker (addOpFunctor k)) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let F' := addOpFunctor k ⋙ F
  let P' : Fan fun n : ℕ ↦ F'.obj (op n) := Fan.mk _ (Pi.π fun n ↦ F'.obj (op n))
  let hP' : IsLimit P' := productIsProduct _
  have hF {a b : ℕ} (f g : op a ⟶ op b) : F.map f = F.map g := by rw [Subsingleton.elim f g]
  have hproj {a b c : ℕ} (hab : a = b) (h₁ : c ≤ a) (h₂ : c ≤ b) :
      P.proj a ≫ F.map (homOfLE h₁).op = P.proj b ≫ F.map (homOfLE h₂).op := by
    subst hab
    rfl
  let p : P.pt ⟶ P'.pt := Fan.IsLimit.lift hP' fun n ↦ P.proj (n + k)
  let q : P'.pt ⟶ P.pt :=
    Fan.IsLimit.lift hP fun n ↦ P'.proj n ≫ F.map (homOfLE (Nat.le_add_right n k)).op
  have hp (n : ℕ) : p ≫ P'.proj n = P.proj (n + k) := Fan.IsLimit.fac hP' _ n
  have hq (n : ℕ) : q ≫ P.proj n = P'.proj n ≫ F.map (homOfLE (Nat.le_add_right n k)).op :=
    Fan.IsLimit.fac hP _ n
  have hpq : p ≫ q = (End.of (towerShift hP) ^ k).asHom :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by rw [assoc, hq, ← assoc, hp, towerShift_pow_proj]
  have hqp : q ≫ p = (End.of (towerShift hP') ^ k).asHom :=
    Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
      rw [assoc, hp, hq, towerShift_pow_proj]
      rfl
  have hpτ : p ≫ (𝟙 _ - towerShift hP') = (𝟙 _ - towerShift hP) ≫ p :=
    Fan.IsLimit.hom_ext hP' _ _ fun n ↦ by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, assoc,
        towerShift_proj, hp]
      rw [← assoc, hp]
      congr 1
      exact hproj (by omega) _ _
  have hqτ : q ≫ (𝟙 _ - towerShift hP) = (𝟙 _ - towerShift hP') ≫ q :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, assoc,
        towerShift_proj, hq]
      rw [← assoc (towerShift hP'), towerShift_proj, ← assoc q, hq]
      simp only [assoc, F', Functor.comp_map, ← Functor.map_comp]
      exact congrArg (fun f ↦ _ - P'.proj (n + 1) ≫ F.map f) (Subsingleton.elim _ _)
  obtain ⟨X, ℓ'', δ'', hT''⟩ := distinguished_cocone_triangle₁ (𝟙 P'.pt - towerShift hP')
  obtain ⟨u, hu₁, hu₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hT hT'' p p hpτ.symm
  obtain ⟨v, hv₁, hv₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hT'' hT q q hqτ.symm
  have hℓ : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ towerShift hP =
      Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) := lift_comp_towerShift hP c
  have hℓpow : ∀ j : ℕ, Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫
      ((End.of (towerShift hP) ^ j).asHom) = Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) := by
    intro j
    induction j with
    | zero => rw [pow_zero, End.one_asHom, comp_id]
    | succ j ih => rw [pow_succ, End.mul_asHom, ← assoc, hℓ, ih]
  have hδ : towerShift hP ≫ δ = δ := by
    have : (𝟙 _ - towerShift hP) ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ hT
    rw [Preadditive.sub_comp, id_comp, sub_eq_zero] at this
    exact this.symm
  have hδpow : ∀ j : ℕ, ((End.of (towerShift hP) ^ j).asHom) ≫ δ = δ := by
    intro j
    induction j with
    | zero => rw [pow_zero, End.one_asHom, id_comp]
    | succ j ih => rw [pow_succ, End.mul_asHom, assoc, ih, hδ]
  have hℓ'' : ℓ'' ≫ towerShift hP' = ℓ'' := by
    have : ℓ'' ≫ (𝟙 _ - towerShift hP') = 0 := comp_distTriang_mor_zero₁₂ _ hT''
    rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at this
    exact this.symm
  have hℓ''pow : ∀ j : ℕ, ℓ'' ≫ ((End.of (towerShift hP') ^ j).asHom) = ℓ'' := by
    intro j
    induction j with
    | zero => rw [pow_zero, End.one_asHom, comp_id]
    | succ j ih => rw [pow_succ, End.mul_asHom, ← assoc, hℓ'', ih]
  have hδ'' : towerShift hP' ≫ δ'' = δ'' := by
    have : (𝟙 _ - towerShift hP') ≫ δ'' = 0 := comp_distTriang_mor_zero₂₃ _ hT''
    rw [Preadditive.sub_comp, id_comp, sub_eq_zero] at this
    exact this.symm
  have hδ''pow : ∀ j : ℕ, ((End.of (towerShift hP') ^ j).asHom) ≫ δ'' = δ'' := by
    intro j
    induction j with
    | zero => rw [pow_zero, End.one_asHom, id_comp]
    | succ j ih => rw [pow_succ, End.mul_asHom, assoc, ih, hδ'']
  let φ : Triangle.mk _ _ δ ⟶ Triangle.mk ℓ'' (𝟙 P'.pt - towerShift hP') δ'' :=
    { hom₁ := u, hom₂ := p, hom₃ := p, comm₁ := hu₁, comm₂ := hpτ.symm, comm₃ := hu₃ }
  let φ' : Triangle.mk ℓ'' (𝟙 P'.pt - towerShift hP') δ'' ⟶ Triangle.mk _ _ δ :=
    { hom₁ := v, hom₂ := q, hom₃ := q, comm₁ := hv₁, comm₂ := hqτ.symm, comm₃ := hv₃ }
  have : IsIso u := isIso_hom₁_of_comp hT hT'' φ φ'
    (by change _ ≫ p ≫ q = _; rw [hpq]; exact hℓpow k)
    (by change p ≫ q ≫ δ = δ; rw [← assoc, hpq, hδpow])
    (by change ℓ'' ≫ q ≫ p = ℓ''; rw [hqp]; exact hℓ''pow k)
    (by change q ≫ p ≫ δ'' = δ''; rw [← assoc, hqp, hδ''pow])
  refine ⟨P', hP', δ'' ≫ (inv u)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT'' _
    (Triangle.isoMk _ _ (asIso u) (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_)⟩
  · have hu₁' : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ p = u ≫ ℓ'' := hu₁
    refine Fan.IsLimit.hom_ext hP' _ _ fun n ↦ ?_
    simp only [Triangle.mk_mor₁, Iso.refl_hom, comp_id, asIso_hom, assoc, Fan.IsLimit.fac]
    rw [← reassoc_of% hu₁', hp, Fan.IsLimit.fac]
    rfl
  · change (δ'' ≫ (inv u)⟦(1 : ℤ)⟧') ≫ u⟦(1 : ℤ)⟧' = 𝟙 _ ≫ δ''
    rw [assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, comp_id,
      id_comp]

end Shift

/-- Isomorphic towers have isomorphic homotopy limits: for `e : F ≅ G` and homotopy limit cones
`c` over `F` and `c'` over `G`, there is an isomorphism `c.pt ≅ c'.pt` compatible with the legs
and with `e`. -/
lemma IsHomotopyLimit.exists_iso_of_iso {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) {c : Cone F} {c' : Cone G}
    (hc : IsHomotopyLimit c) (hc' : IsHomotopyLimit c') :
    ∃ f : c.pt ≅ c'.pt, ∀ n : ℕ,
      f.hom ≫ c'.π.app (op n) = c.π.app (op n) ≫ e.hom.app (op n) := by
  let c'' : Cone G := { pt := c.pt, π := c.π ≫ e.hom }
  have hc'' : IsHomotopyLimit c'' := hc.of_iso e c'' (Iso.refl _) fun n ↦ by
    simp [c'']
  obtain ⟨f, hf⟩ := hc''.exists_iso hc'
  exact ⟨f, fun n ↦ by rw [hf]; rfl⟩

end CategoryTheory.Pretriangulated
