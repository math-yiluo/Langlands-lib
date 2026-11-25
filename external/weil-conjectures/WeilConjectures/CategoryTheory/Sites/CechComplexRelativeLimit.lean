/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Pro.Basic
public import WeilConjectures.CategoryTheory.Sites.CohomologyFilteredColimit

/-!
# Čech complexes along a cofiltered limit of morphisms

Let `F : C' ⥤ C` be a functor and `q : W ⟶ V` a morphism of `C` which is a cofiltered limit
`q = limⱼ F(αⱼ)` of morphisms `αⱼ : Wⱼ ⟶ Vⱼ` of `C'`, presented by relative limit presentations
of `W` and `V` (`CategoryTheory.Limits.RelativeLimitPresentation`). The fibre powers
`W ×_V ⋯ ×_V W` are then the cofiltered limits of the images of the fibre powers
`Wⱼ ×_{Vⱼ} ⋯ ×_{Vⱼ} Wⱼ`, as long as `F` preserves these fibre powers
(`CategoryTheory.Presheaf.isLimitStageNerveCone`).

Consequently, if a presheaf `P` on `C` sends such cofiltered limits to colimits, the Čech
complex of `P` for the single morphism `q` is the filtered colimit of the Čech complexes of
`F.op ⋙ P` for the `αⱼ`, and it is exact in positive degrees as soon as all the latter are
(`CategoryTheory.Presheaf.exactAt_cechComplex_of_relativeLimitPresentation`).

## Main statements

- `CategoryTheory.Presheaf.isLimitStageNerveCone`: fibre powers commute with the cofiltered
  limit.
- `CategoryTheory.Presheaf.exactAt_cechComplex_of_relativeLimitPresentation`: exactness of Čech
  complexes passes to the limit.
-/

@[expose] public section

universe t w v

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Over

variable {C : Type*} [Category* C] {X : C} {ι : Type*} {f : ι → Over X}

/-- Morphisms into the underlying object of a limit fan in `Over X` are determined by their
composites with the structure morphism and with the projections. -/
lemma Fan.left_hom_ext {c : Fan f} (hc : IsLimit c) {T : C} {a b : T ⟶ c.pt.left}
    (h₀ : a ≫ c.pt.hom = b ≫ c.pt.hom)
    (h : ∀ l, a ≫ (c.proj l).left = b ≫ (c.proj l).left) : a = b := by
  let a' : Over.mk (a ≫ c.pt.hom) ⟶ c.pt := Over.homMk a rfl
  let b' : Over.mk (a ≫ c.pt.hom) ⟶ c.pt := Over.homMk b h₀.symm
  have : a' = b' := Fan.IsLimit.hom_ext hc _ _ fun l ↦ Over.OverMorphism.ext (by
    simpa [a', b'] using h l)
  exact congrArg CommaMorphism.left this

/-- A morphism into the underlying object of a limit fan in `Over X`, given by morphisms into
the underlying objects of the factors which agree over `X`. -/
noncomputable def Fan.leftLift {c : Fan f} (hc : IsLimit c) {T : C} (τ : T ⟶ X)
    (s : ∀ l, T ⟶ (f l).left) (hs : ∀ l, s l ≫ (f l).hom = τ) : T ⟶ c.pt.left :=
  (hc.lift (Fan.mk (Over.mk τ) fun l ↦ Over.homMk (s l) (hs l))).left

@[reassoc (attr := simp)]
lemma Fan.leftLift_hom {c : Fan f} (hc : IsLimit c) {T : C} (τ : T ⟶ X)
    (s : ∀ l, T ⟶ (f l).left) (hs : ∀ l, s l ≫ (f l).hom = τ) :
    Fan.leftLift hc τ s hs ≫ c.pt.hom = τ :=
  Over.w (hc.lift (Fan.mk (Over.mk τ) fun l ↦ Over.homMk (s l) (hs l)))

@[reassoc (attr := simp)]
lemma Fan.leftLift_proj {c : Fan f} (hc : IsLimit c) {T : C} (τ : T ⟶ X)
    (s : ∀ l, T ⟶ (f l).left) (hs : ∀ l, s l ≫ (f l).hom = τ) (l : ι) :
    Fan.leftLift hc τ s hs ≫ (c.proj l).left = s l := by
  have := hc.fac (Fan.mk (Over.mk τ) fun l ↦ Over.homMk (s l) (hs l)) ⟨l⟩
  exact congrArg CommaMorphism.left this

variable [HasProduct f]

/-- A morphism into the underlying object of a product in `Over X`, given by morphisms into the
underlying objects of the factors which agree over `X`. -/
noncomputable def piLeftLift {T : C} (τ : T ⟶ X) (s : ∀ l, T ⟶ (f l).left)
    (hs : ∀ l, s l ≫ (f l).hom = τ) : T ⟶ (∏ᶜ f).left :=
  Fan.leftLift (productIsProduct f) τ s hs

@[reassoc (attr := simp)]
lemma piLeftLift_hom {T : C} (τ : T ⟶ X) (s : ∀ l, T ⟶ (f l).left)
    (hs : ∀ l, s l ≫ (f l).hom = τ) : piLeftLift τ s hs ≫ (∏ᶜ f).hom = τ :=
  Fan.leftLift_hom (productIsProduct f) τ s hs

@[reassoc (attr := simp)]
lemma piLeftLift_π {T : C} (τ : T ⟶ X) (s : ∀ l, T ⟶ (f l).left)
    (hs : ∀ l, s l ≫ (f l).hom = τ) (l : ι) : piLeftLift τ s hs ≫ (Pi.π f l).left = s l :=
  Fan.leftLift_proj (productIsProduct f) τ s hs l

/-- Morphisms into the underlying object of a product in `Over X` are determined by their
composites with the structure morphism and with the projections. -/
lemma pi_left_hom_ext {T : C} {a b : T ⟶ (∏ᶜ f).left} (h₀ : a ≫ (∏ᶜ f).hom = b ≫ (∏ᶜ f).hom)
    (hl : ∀ l, a ≫ (Pi.π f l).left = b ≫ (Pi.π f l).left) : a = b :=
  Fan.left_hom_ext (productIsProduct f) h₀ hl

end Over

namespace Presheaf

section CochainMap

variable {C₁ : Type w} [Category.{v} C₁] {C₂ : Type w} [Category.{v} C₂] {V₁ : C₁} {V₂ : C₂}
  [HasFiniteProducts (Over V₁)] [HasFiniteProducts (Over V₂)] {ι : Type t}
  (U₁ : ι → Over V₁) (U₂ : ι → Over V₂)
  (P₁ : C₁ᵒᵖ ⥤ AddCommGrpCat.{max w v}) (P₂ : C₂ᵒᵖ ⥤ AddCommGrpCat.{max w v})

/-- Maps between the members of two Čech nerves, compatible with the face maps, induce a map
of Čech cochains which commutes with the Čech differentials. -/
lemma cechComplex_d_cochainMap
    (ψ : ∀ {k : ℕ} (y : Fin (k + 1) → ι),
      P₁.obj (op (cechNerveObj U₁ y).left) →+ P₂.obj (op (cechNerveObj U₂ y).left))
    (hψ : ∀ {k : ℕ} (y : Fin (k + 2) → ι) (i : Fin (k + 2))
      (x : P₁.obj (op (cechNerveObj U₁ (y ∘ i.succAbove)).left)),
      ψ y (P₁.map (cechNerveMap U₁ y i.succAbove).left.op x) =
        P₂.map (cechNerveMap U₂ y i.succAbove).left.op (ψ (y ∘ i.succAbove) x))
    (k : ℕ) (c : ((cechComplex U₁).obj P₁).X k) :
    (((cechComplex U₂).obj P₂).d k (k + 1) fun y ↦ ψ y (c y)) =
      fun y ↦ ψ y (((cechComplex U₁).obj P₁).d k (k + 1) c y) := by
  funext y
  rw [cechComplex_d_apply, cechComplex_d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, hψ]

end CochainMap

section RelativeLimit

/-- The face maps of a Čech nerve, on underlying objects, followed by a projection. -/
@[reassoc (attr := simp)]
lemma cechNerveMap_left_π {C : Type*} [Category* C] {V : C} [HasFiniteProducts (Over V)]
    {ι : Type*} (U : ι → Over V) {k m : ℕ} (y : Fin (m + 1) → ι)
    (θ : Fin (k + 1) → Fin (m + 1)) (l : Fin (k + 1)) :
    (cechNerveMap U y θ).left ≫ (Pi.π (fun l ↦ U ((y ∘ θ) l)) l).left =
      (Pi.π (fun l ↦ U (y l)) (θ l)).left := by
  rw [← Over.comp_left]
  exact congrArg CommaMorphism.left (cechNerveMap_π U y θ l)

variable {C' : Type w} [Category.{v} C'] {C : Type w} [Category.{v} C] {F : C' ⥤ C}
  {J : Type t} [Category J] {V W : C}
  {pV : RelativeLimitPresentation J F V} {pW : RelativeLimitPresentation J F W}
  (h : pW.Hom pV)

/-- The `j`-th stage `αⱼ : Wⱼ ⟶ Vⱼ` of a cofiltered limit of morphisms, as a one-member family
over `Vⱼ`. -/
abbrev stageFamily (j : J) : Fin 1 → Over (pV.diag.obj j) :=
  fun _ ↦ Over.mk (h.natTrans.app j)

/-- The limit morphism `q : W ⟶ V`, as a one-member family over `V`. -/
abbrev limitFamily : Fin 1 → Over V :=
  fun _ ↦ Over.mk h.map

@[reassoc]
lemma stageNerve_π_natTrans (j : J) [HasFiniteProducts (Over (pV.diag.obj j))] {k : ℕ}
    (y : Fin (k + 1) → Fin 1) (l : Fin (k + 1)) :
    (Pi.π (fun l ↦ stageFamily h j (y l)) l).left ≫ h.natTrans.app j =
      (cechNerveObj (stageFamily h j) y).hom :=
  Over.w (Pi.π (fun l ↦ stageFamily h j (y l)) l)

@[reassoc]
lemma limitNerve_π_map [HasFiniteProducts (Over V)] {k : ℕ} (y : Fin (k + 1) → Fin 1)
    (l : Fin (k + 1)) :
    (Pi.π (fun l ↦ limitFamily h (y l)) l).left ≫ h.map =
      (cechNerveObj (limitFamily h) y).hom :=
  Over.w (Pi.π (fun l ↦ limitFamily h (y l)) l)

variable [∀ j, HasFiniteProducts (Over (pV.diag.obj j))]

/-- The transition maps between the fibre powers `Wⱼ ×_{Vⱼ} ⋯ ×_{Vⱼ} Wⱼ`. -/
noncomputable def stageNerveMap {i j : J} (g : i ⟶ j) {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    (cechNerveObj (stageFamily h i) y).left ⟶ (cechNerveObj (stageFamily h j) y).left :=
  Over.piLeftLift ((cechNerveObj (stageFamily h i) y).hom ≫ pV.diag.map g)
    (fun l ↦ (Pi.π (fun l ↦ stageFamily h i (y l)) l).left ≫ pW.diag.map g) fun l ↦ by
      change ((Pi.π (fun l ↦ stageFamily h i (y l)) l).left ≫ pW.diag.map g) ≫
        h.natTrans.app j = (cechNerveObj (stageFamily h i) y).hom ≫ pV.diag.map g
      rw [Category.assoc, h.natTrans.naturality g, stageNerve_π_natTrans_assoc]

@[reassoc (attr := simp)]
lemma stageNerveMap_hom {i j : J} (g : i ⟶ j) {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    stageNerveMap h g y ≫ (cechNerveObj (stageFamily h j) y).hom =
      (cechNerveObj (stageFamily h i) y).hom ≫ pV.diag.map g :=
  Over.piLeftLift_hom _ _ _

@[reassoc (attr := simp)]
lemma stageNerveMap_π {i j : J} (g : i ⟶ j) {k : ℕ} (y : Fin (k + 1) → Fin 1)
    (l : Fin (k + 1)) :
    stageNerveMap h g y ≫ (Pi.π (fun l ↦ stageFamily h j (y l)) l).left =
      (Pi.π (fun l ↦ stageFamily h i (y l)) l).left ≫ pW.diag.map g :=
  Over.piLeftLift_π _ _ _ l

/-- The diagram `j ↦ Wⱼ ×_{Vⱼ} ⋯ ×_{Vⱼ} Wⱼ` of fibre powers of the stages. -/
@[simps]
noncomputable def stageNerve {k : ℕ} (y : Fin (k + 1) → Fin 1) : J ⥤ C' where
  obj j := (cechNerveObj (stageFamily h j) y).left
  map g := stageNerveMap h g y
  map_id j := Over.pi_left_hom_ext (by simp) fun l ↦ by simp
  map_comp g g' := Over.pi_left_hom_ext (by simp) fun l ↦ by simp

/-- The stage nerve maps commute with the face maps of the Čech nerves. -/
@[reassoc]
lemma stageNerveMap_cechNerveMap {i j : J} (g : i ⟶ j) {k m : ℕ} (y : Fin (m + 1) → Fin 1)
    (θ : Fin (k + 1) → Fin (m + 1)) :
    stageNerveMap h g y ≫ (cechNerveMap (stageFamily h j) y θ).left =
      (cechNerveMap (stageFamily h i) y θ).left ≫ stageNerveMap h g (y ∘ θ) := by
  refine Over.pi_left_hom_ext ?_ fun l ↦ ?_
  · rw [Category.assoc, Over.w, stageNerveMap_hom, Category.assoc, stageNerveMap_hom,
      Over.w_assoc]
  · rw [Category.assoc, Category.assoc, cechNerveMap_left_π, stageNerveMap_π, stageNerveMap_π,
      cechNerveMap_left_π_assoc]

variable [HasFiniteProducts (Over V)]
  [∀ j, PreservesFiniteProducts (Over.post F (X := pV.diag.obj j))]

/-- The image under `F` of the fibre power `Wⱼ ×_{Vⱼ} ⋯ ×_{Vⱼ} Wⱼ`, as a limit fan in
`Over (F Vⱼ)`. -/
noncomputable def stageNerveFanIsLimit (j : J) {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    IsLimit (Fan.mk ((Over.post F).obj (cechNerveObj (stageFamily h j) y))
      fun l ↦ (Over.post F).map (Pi.π (fun l ↦ stageFamily h j (y l)) l)) :=
  isLimitFanMkObjOfIsLimit (Over.post F) _ _ (productIsProduct _)

omit [HasFiniteProducts (Over V)] in
lemma stageNerve_map_hom_ext {j : J} {k : ℕ} {y : Fin (k + 1) → Fin 1} {T : C}
    {a b : T ⟶ F.obj (cechNerveObj (stageFamily h j) y).left}
    (h₀ : a ≫ F.map (cechNerveObj (stageFamily h j) y).hom =
      b ≫ F.map (cechNerveObj (stageFamily h j) y).hom)
    (hl : ∀ l, a ≫ F.map (Pi.π (fun l ↦ stageFamily h j (y l)) l).left =
      b ≫ F.map (Pi.π (fun l ↦ stageFamily h j (y l)) l).left) : a = b :=
  Over.Fan.left_hom_ext (stageNerveFanIsLimit h j y) h₀ hl

/-- The projection `W ×_V ⋯ ×_V W ⟶ F(Wⱼ ×_{Vⱼ} ⋯ ×_{Vⱼ} Wⱼ)`. -/
noncomputable def limitNerveLeg (j : J) {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    (cechNerveObj (limitFamily h) y).left ⟶ F.obj (cechNerveObj (stageFamily h j) y).left :=
  Over.Fan.leftLift (stageNerveFanIsLimit h j y)
    ((cechNerveObj (limitFamily h) y).hom ≫ pV.π.app j)
    (fun l ↦ (Pi.π (fun l ↦ limitFamily h (y l)) l).left ≫ pW.π.app j) fun l ↦ by
      change ((Pi.π (fun l ↦ limitFamily h (y l)) l).left ≫ pW.π.app j) ≫
        F.map (h.natTrans.app j) = (cechNerveObj (limitFamily h) y).hom ≫ pV.π.app j
      rw [Category.assoc, ← RelativeLimitPresentation.Hom.map_π, limitNerve_π_map_assoc]

@[reassoc (attr := simp)]
lemma limitNerveLeg_hom (j : J) {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    limitNerveLeg h j y ≫ F.map (cechNerveObj (stageFamily h j) y).hom =
      (cechNerveObj (limitFamily h) y).hom ≫ pV.π.app j :=
  Over.Fan.leftLift_hom (stageNerveFanIsLimit h j y) _ _ _

@[reassoc (attr := simp)]
lemma limitNerveLeg_π (j : J) {k : ℕ} (y : Fin (k + 1) → Fin 1) (l : Fin (k + 1)) :
    limitNerveLeg h j y ≫ F.map (Pi.π (fun l ↦ stageFamily h j (y l)) l).left =
      (Pi.π (fun l ↦ limitFamily h (y l)) l).left ≫ pW.π.app j :=
  Over.Fan.leftLift_proj (stageNerveFanIsLimit h j y) _ _ _ l

/-- The projections to the stages commute with the face maps of the Čech nerves. -/
@[reassoc]
lemma limitNerveLeg_cechNerveMap (j : J) {k m : ℕ} (y : Fin (m + 1) → Fin 1)
    (θ : Fin (k + 1) → Fin (m + 1)) :
    limitNerveLeg h j y ≫ F.map (cechNerveMap (stageFamily h j) y θ).left =
      (cechNerveMap (limitFamily h) y θ).left ≫ limitNerveLeg h j (y ∘ θ) := by
  refine stageNerve_map_hom_ext h ?_ fun l ↦ ?_
  · rw [Category.assoc, ← F.map_comp, Over.w, limitNerveLeg_hom, Category.assoc,
      limitNerveLeg_hom, Over.w_assoc]
  · rw [Category.assoc, ← F.map_comp, cechNerveMap_left_π, limitNerveLeg_π, Category.assoc,
      limitNerveLeg_π, cechNerveMap_left_π_assoc]

omit [HasFiniteProducts (Over V)] in
lemma π_app_map_eq {X : C} {p : RelativeLimitPresentation J F X} {i j : J} (g : i ⟶ j) :
    p.π.app i ≫ F.map (p.diag.map g) = p.π.app j :=
  (p.π.naturality g).symm.trans (Category.id_comp _)

/-- The projections to the stages are compatible with the transition maps. -/
@[reassoc (attr := simp)]
lemma limitNerveLeg_stageNerveMap {i j : J} (g : i ⟶ j) {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    limitNerveLeg h i y ≫ F.map (stageNerveMap h g y) = limitNerveLeg h j y := by
  refine stageNerve_map_hom_ext h ?_ fun l ↦ ?_
  · rw [Category.assoc, ← F.map_comp, stageNerveMap_hom, F.map_comp, limitNerveLeg_hom_assoc,
      limitNerveLeg_hom, π_app_map_eq]
  · rw [Category.assoc, ← F.map_comp, stageNerveMap_π, F.map_comp, limitNerveLeg_π_assoc,
      limitNerveLeg_π, π_app_map_eq]

/-- The cone exhibiting `W ×_V ⋯ ×_V W` as the limit of the `F(Wⱼ ×_{Vⱼ} ⋯ ×_{Vⱼ} Wⱼ)`. -/
@[simps]
noncomputable def stageNerveCone {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    Cone (stageNerve h y ⋙ F) where
  pt := (cechNerveObj (limitFamily h) y).left
  π :=
    { app j := limitNerveLeg h j y
      naturality i j g := by
        change 𝟙 _ ≫ limitNerveLeg h j y = limitNerveLeg h i y ≫ F.map (stageNerveMap h g y)
        rw [Category.id_comp, limitNerveLeg_stageNerveMap] }

/-- **Fibre powers commute with cofiltered limits.** The fibre power `W ×_V ⋯ ×_V W` of the
limit morphism `q : W ⟶ V` is the limit of the images of the fibre powers of the stages. -/
noncomputable def isLimitStageNerveCone {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    IsLimit (stageNerveCone h y) := by
  have hs (s : Cone (stageNerve h y ⋙ F)) {i j : J} (g : i ⟶ j) :
      s.π.app j = s.π.app i ≫ F.map (stageNerveMap h g y) :=
    (Category.id_comp _).symm.trans (s.π.naturality g)
  let τ (s : Cone (stageNerve h y ⋙ F)) : s.pt ⟶ V :=
    pV.isLimit.lift ⟨s.pt,
      { app j := s.π.app j ≫ F.map (cechNerveObj (stageFamily h j) y).hom
        naturality i j g := by
          change 𝟙 s.pt ≫ s.π.app j ≫ F.map (cechNerveObj (stageFamily h j) y).hom =
            (s.π.app i ≫ F.map (cechNerveObj (stageFamily h i) y).hom) ≫ F.map (pV.diag.map g)
          rw [Category.id_comp, hs s g, Category.assoc, ← F.map_comp, stageNerveMap_hom,
            F.map_comp, Category.assoc] }⟩
  let σ (s : Cone (stageNerve h y ⋙ F)) (l : Fin (k + 1)) : s.pt ⟶ W :=
    pW.isLimit.lift ⟨s.pt,
      { app j := s.π.app j ≫ F.map (Pi.π (fun l ↦ stageFamily h j (y l)) l).left
        naturality i j g := by
          change 𝟙 s.pt ≫ s.π.app j ≫ F.map (Pi.π (fun l ↦ stageFamily h j (y l)) l).left =
            (s.π.app i ≫ F.map (Pi.π (fun l ↦ stageFamily h i (y l)) l).left) ≫
              F.map (pW.diag.map g)
          rw [Category.id_comp, hs s g, Category.assoc, ← F.map_comp, stageNerveMap_π,
            F.map_comp, Category.assoc] }⟩
  have hτ (s : Cone (stageNerve h y ⋙ F)) (j : J) :
      τ s ≫ pV.π.app j = s.π.app j ≫ F.map (cechNerveObj (stageFamily h j) y).hom :=
    pV.isLimit.fac _ j
  have hσ (s : Cone (stageNerve h y ⋙ F)) (l : Fin (k + 1)) (j : J) :
      σ s l ≫ pW.π.app j = s.π.app j ≫ F.map (Pi.π (fun l ↦ stageFamily h j (y l)) l).left :=
    pW.isLimit.fac _ j
  have hστ (s : Cone (stageNerve h y ⋙ F)) (l : Fin (k + 1)) : σ s l ≫ h.map = τ s := by
    refine pV.isLimit.hom_ext fun j ↦ ?_
    rw [Category.assoc, RelativeLimitPresentation.Hom.map_π, reassoc_of% hσ, hτ,
      ← F.map_comp, stageNerve_π_natTrans]
  exact
    { lift s := Over.piLeftLift (τ s) (σ s) (hστ s)
      fac s j := by
        change Over.piLeftLift (τ s) (σ s) (hστ s) ≫ limitNerveLeg h j y = s.π.app j
        refine stageNerve_map_hom_ext h ?_ fun l ↦ ?_
        · rw [Category.assoc, limitNerveLeg_hom, Over.piLeftLift_hom_assoc, hτ]
        · rw [Category.assoc, limitNerveLeg_π, Over.piLeftLift_π_assoc, hσ]
      uniq s m hm := by
        have hm' (j : J) : m ≫ limitNerveLeg h j y = s.π.app j := hm j
        refine Over.pi_left_hom_ext ?_ fun l ↦ ?_
        · rw [Over.piLeftLift_hom]
          refine pV.isLimit.hom_ext fun j ↦ ?_
          rw [hτ, Category.assoc, ← limitNerveLeg_hom, ← hm' j, Category.assoc]
        · rw [Over.piLeftLift_π]
          refine pW.isLimit.hom_ext fun j ↦ ?_
          rw [hσ, Category.assoc, ← limitNerveLeg_π, ← hm' j, Category.assoc] }

end RelativeLimit

section Exactness

variable {C' : Type w} [Category.{v} C'] {C : Type w} [Category.{v} C] {F : C' ⥤ C}
  {J : Type t} [SmallCategory J] {V W : C}
  {pV : RelativeLimitPresentation J F V} {pW : RelativeLimitPresentation J F W}
  (h : pW.Hom pV) [∀ j, HasFiniteProducts (Over (pV.diag.obj j))] [HasFiniteProducts (Over V)]
  [∀ j, PreservesFiniteProducts (Over.post F (X := pV.diag.obj j))]
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})

/-- The map from the Čech cochains of `F.op ⋙ P` for the stage `αⱼ` to the Čech cochains of
`P` for the limit morphism, induced by the projections `limitNerveLeg`. -/
noncomputable def stageCochainMap (j : J) (k : ℕ) :
    CechCochain (stageFamily h j) (F.op ⋙ P) k →+ CechCochain (limitFamily h) P k :=
  AddMonoidHom.pi fun y ↦ (P.map (limitNerveLeg h j y).op).hom.comp (Pi.evalAddMonoidHom _ y)

lemma stageCochainMap_apply (j : J) {k : ℕ} (c : CechCochain (stageFamily h j) (F.op ⋙ P) k)
    (y : Fin (k + 1) → Fin 1) :
    stageCochainMap h P j k c y = P.map (limitNerveLeg h j y).op (c y) :=
  rfl

/-- The transition map between the Čech cochains of `F.op ⋙ P` for two stages. -/
noncomputable def stageTransitionCochainMap {i j : J} (g : i ⟶ j) (k : ℕ) :
    CechCochain (stageFamily h j) (F.op ⋙ P) k →+ CechCochain (stageFamily h i) (F.op ⋙ P) k :=
  AddMonoidHom.pi fun y ↦
    (P.map (F.map (stageNerveMap h g y)).op).hom.comp (Pi.evalAddMonoidHom _ y)

omit [HasFiniteProducts (Over V)]
  [∀ j, PreservesFiniteProducts (Over.post F (X := pV.diag.obj j))] in
lemma stageTransitionCochainMap_apply {i j : J} (g : i ⟶ j) {k : ℕ}
    (c : CechCochain (stageFamily h j) (F.op ⋙ P) k) (y : Fin (k + 1) → Fin 1) :
    stageTransitionCochainMap h P g k c y = P.map (F.map (stageNerveMap h g y)).op (c y) :=
  rfl

lemma stageCochainMap_d (j : J) (k : ℕ)
    (c : ((cechComplex (stageFamily h j)).obj (F.op ⋙ P)).X k) :
    ((cechComplex (limitFamily h)).obj P).d k (k + 1) (stageCochainMap h P j k c) =
      stageCochainMap h P j (k + 1) (((cechComplex (stageFamily h j)).obj (F.op ⋙ P)).d k
        (k + 1) c) :=
  cechComplex_d_cochainMap (stageFamily h j) (limitFamily h) (F.op ⋙ P) P
    (fun y ↦ (P.map (limitNerveLeg h j y).op).hom) (fun y i x ↦ by
      change P.map (limitNerveLeg h j y).op (P.map (F.map (cechNerveMap _ y _).left).op x) =
        P.map (cechNerveMap _ y _).left.op (P.map (limitNerveLeg h j _).op x)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P.map_comp,
        ← P.map_comp, ← op_comp, ← op_comp, limitNerveLeg_cechNerveMap]) k c

omit [HasFiniteProducts (Over V)]
  [∀ j, PreservesFiniteProducts (Over.post F (X := pV.diag.obj j))] in
lemma stageTransitionCochainMap_d {i j : J} (g : i ⟶ j) (k : ℕ)
    (c : ((cechComplex (stageFamily h j)).obj (F.op ⋙ P)).X k) :
    ((cechComplex (stageFamily h i)).obj (F.op ⋙ P)).d k (k + 1)
        (stageTransitionCochainMap h P g k c) =
      stageTransitionCochainMap h P g (k + 1)
        (((cechComplex (stageFamily h j)).obj (F.op ⋙ P)).d k (k + 1) c) :=
  cechComplex_d_cochainMap (stageFamily h j) (stageFamily h i) (F.op ⋙ P) (F.op ⋙ P)
    (fun y ↦ (P.map (F.map (stageNerveMap h g y)).op).hom) (fun y l x ↦ by
      change P.map (F.map (stageNerveMap h g y)).op (P.map (F.map (cechNerveMap _ y _).left).op x)
        = P.map (F.map (cechNerveMap _ y _).left).op
          (P.map (F.map (stageNerveMap h g _)).op x)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P.map_comp,
        ← P.map_comp, ← op_comp, ← op_comp, ← F.map_comp, ← F.map_comp,
        stageNerveMap_cechNerveMap]) k c

lemma stageCochainMap_stageTransitionCochainMap {i j : J} (g : i ⟶ j) (k : ℕ)
    (c : CechCochain (stageFamily h j) (F.op ⋙ P) k) :
    stageCochainMap h P i k (stageTransitionCochainMap h P g k c) = stageCochainMap h P j k c := by
  funext y
  change P.map (limitNerveLeg h i y).op (P.map (F.map (stageNerveMap h g y)).op (c y)) =
    P.map (limitNerveLeg h j y).op (c y)
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, limitNerveLeg_stageNerveMap]

variable [IsCofiltered J]

/-- **Čech complexes along a cofiltered limit of morphisms.** Let `q : W ⟶ V` be the cofiltered
limit of morphisms `αⱼ : Wⱼ ⟶ Vⱼ` of `C'` under `F : C' ⥤ C`, and let `P` be a presheaf on `C`
sending such cofiltered limits to filtered colimits. If the Čech complexes of `F.op ⋙ P` for all
the `αⱼ` are exact in positive degrees, so is the Čech complex of `P` for `q`: it is the filtered
colimit of the former. -/
theorem exactAt_cechComplex_of_relativeLimitPresentation
    [F.PreservesRelativeFilteredColimits.{t} P]
    (hstage : ∀ (j : J) (q : ℕ),
      ((cechComplex (stageFamily h j)).obj (F.op ⋙ P)).ExactAt (q + 1))
    (q : ℕ) : ((cechComplex (limitFamily h)).obj P).ExactAt (q + 1) := by
  have hcol {k : ℕ} (y : Fin (k + 1) → Fin 1) :=
    (Functor.PreservesRelativeFilteredColimits.nonempty_isColimit (F := F) (P := P)
      (stageNerveCone h y) (isLimitStageNerveCone h y)).some
  rw [exactAt_cechComplex_iff]
  intro c hc
  let y₀ : Fin (q + 2) → Fin 1 := fun _ ↦ 0
  let y₁ : Fin (q + 3) → Fin 1 := fun _ ↦ 0
  obtain ⟨⟨j⟩, x₀, hx₀⟩ := AddCommGrpCat.exists_ι_apply_eq_of_isColimit (hcol y₀) (c y₀)
  let x : ((cechComplex (stageFamily h j)).obj (F.op ⋙ P)).X (q + 1) := fun _ ↦ x₀
  have hx : stageCochainMap h P j (q + 1) x = c := by
    funext y
    obtain rfl : y = y₀ := Subsingleton.elim _ _
    exact hx₀
  -- the differential of `x` vanishes in the colimit, hence at some later stage
  have hdx : P.map (limitNerveLeg h j y₁).op
      ((((cechComplex (stageFamily h j)).obj (F.op ⋙ P)).d (q + 1) (q + 2) x) y₁) = 0 := by
    have := congrFun ((stageCochainMap_d h P j (q + 1) x).symm.trans
      ((congrArg _ hx).trans hc)) y₁
    exact this
  obtain ⟨⟨j'⟩, a, ha⟩ := AddCommGrpCat.exists_map_eq_zero_of_isColimit (hcol y₁) _ hdx
  let g : j' ⟶ j := a.unop
  let x' := stageTransitionCochainMap h P g (q + 1) x
  have hx' : ((cechComplex (stageFamily h j')).obj (F.op ⋙ P)).d (q + 1) (q + 2) x' = 0 := by
    rw [stageTransitionCochainMap_d]
    funext y
    obtain rfl : y = y₁ := Subsingleton.elim _ _
    exact ha
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff _ _ _).1 (hstage j' q) x' hx'
  refine ⟨stageCochainMap h P j' q b, ?_⟩
  rw [stageCochainMap_d, hb, ← hx]
  exact stageCochainMap_stageTransitionCochainMap h P g (q + 1) x

end Exactness

end Presheaf

end CategoryTheory
