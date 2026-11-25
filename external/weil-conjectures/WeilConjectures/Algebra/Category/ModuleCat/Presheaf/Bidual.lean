/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-!
# The biduality morphism of presheaves of modules

Let `R : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings on a category `C`. For a presheaf
of modules `A` over `R`, the biduality morphism `A ⟶ Hom(Hom(A, R), R)` sends a section `m` to
evaluation at `m` (`PresheafOfModules.bidual`). It is natural in `A`
(`PresheafOfModules.bidual_naturality`), and it is bijective on sections over `U` if `A` is free
of finite rank on `U` (`PresheafOfModules.bidual_app_bijective`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (A : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

/-- The biduality morphism `A ⟶ Hom(Hom(A, R), R)`, sending a section `m` to evaluation at
`m`. -/
noncomputable def bidual : A ⟶ homObj (homObj A (unit _)) (unit _) :=
  tensorHomCurry ((β_ (homObj A (unit _)) A).hom ≫ tensorHomUncurry (𝟙 _))

lemma bidual_app_app_apply {X : Cᵒᵖ} (m : A.obj X) (W : (Over X.unop)ᵒᵖ)
    (φ : (homObj A (unit _)).obj (op W.unop.left)) :
    (((bidual A).app X m).app W) φ =
      φ.app (op (Over.mk (𝟙 W.unop.left))) (A.map W.unop.hom.op m) :=
  rfl


variable {A} in
/-- The biduality morphism is natural. -/
@[reassoc]
lemma bidual_naturality {A' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : A ⟶ A') :
    f ≫ bidual A' = bidual A ≫ homObjMap (homObjMap f (𝟙 _)) (𝟙 _) := by
  ext X m : 3
  refine hom_ext (M₁ := (restrictOver R X.unop).obj (homObj A' (unit _)))
    (M₂ := (restrictOver R X.unop).obj (unit _)) fun W ↦ ?_
  ext φ
  change φ.app (op (Over.mk (𝟙 W.unop.left))) (A'.map W.unop.hom.op (f.app X m)) =
    φ.app (op (Over.mk (𝟙 W.unop.left))) (f.app (op W.unop.left) (A.map W.unop.hom.op m))
  rw [naturality_apply]

section Bijective

variable {D : Type*} [Category D] {S : Dᵒᵖ ⥤ RingCat.{u}}

lemma sum_app_apply {M N : PresheafOfModules.{u} S} {ι : Type*} (t : Finset ι) (f : ι → (M ⟶ N))
    (X : Dᵒᵖ) (x : M.obj X) : (∑ i ∈ t, f i).app X x = ∑ i ∈ t, (f i).app X x :=
  map_sum ({ toFun f := f.app X x, map_zero' := rfl, map_add' _ _ := rfl } :
    (M ⟶ N) →+ N.obj X) f t

end Bijective

variable {A} {U : C}

/-- A morphism `R|_U ⟶ A|_U` sends `r` to `r` times the restriction of the image of `1`. -/
lemma app_unit_eq_smul (s : (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj A)
    (W : (Over U)ᵒᵖ) (r : R.obj (op W.unop.left)) :
    s.app W r = r • (show A.obj (op W.unop.left) from
      A.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)))) := by
  have h1 : s.app W (1 : R.obj (op W.unop.left)) =
      A.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U))) :=
    (congrArg (s.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op).symm).trans
      (naturality_apply s
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op _)
  refine (congrArg (s.app W) (mul_one r).symm).trans ?_
  refine ((s.app W).hom.map_smul r (1 : R.obj (op W.unop.left))).trans ?_
  exact congrArg (fun y : A.obj (op W.unop.left) ↦ r • y) h1

/-- **Biduality for free presheaves of modules of finite rank.** If `A` is free of finite rank
on `U`, i.e. `A|_U` is a finite direct sum of copies of `R|_U` with inclusions `s i` and
projections `c i`, then the biduality morphism is bijective on sections over `U`. -/
lemma bidual_app_bijective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj A))
    (c : ι → ((restrictOver R U).obj A ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) :
    Function.Bijective ((bidual A).app (op U)) := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let m : ι → A.obj (op U) := fun i ↦ (s i).app T (1 : R.obj (op U))
  -- Every section of `A` over `W ⟶ U` is a combination of the restrictions of the `m i`.
  have hspan (W : (Over U)ᵒᵖ) (x : A.obj (op W.unop.left)) :
      x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show A.obj (op W.unop.left) from A.map W.unop.hom.op (m i)) := by
    have h : ∑ i, (c i ≫ s i).app W x = x :=
      (sum_app_apply Finset.univ (fun i ↦ c i ≫ s i) W x).symm.trans
        (congrArg (fun f ↦ f.app W x) htot)
    exact h.symm.trans (Finset.sum_congr rfl fun i _ ↦ app_unit_eq_smul (s i) W _)
  have hcm (i j : ι) : (c i).app T (m j) = if j = i then (1 : R.obj (op U)) else 0 := by
    have h := congrArg (fun f ↦ f.app T (1 : R.obj (op U))) (hsc i j)
    refine h.trans ?_
    split_ifs <;> rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hc (i : ι) : (c i).app T x = 0 := by
      have h := congrArg (fun Φ ↦ Φ.app T (c i)) hx
      refine Eq.trans ?_ h
      refine congrArg ((c i).app T) (A.map_id_apply' x).symm
    refine (hspan T x).trans (Finset.sum_eq_zero fun i _ ↦ ?_)
    change (show R.obj (op U) from (c i).app T x) • _ = (0 : A.obj (op U))
    dsimp only
    rw [hc]
    exact zero_smul _ _
  · intro Ψ
    let a : ι → R.obj (op U) := fun i ↦ Ψ.app T (c i)
    refine ⟨∑ i, a i • m i, ?_⟩
    refine hom_ext (M₁ := (restrictOver R U).obj (homObj A (unit _)))
      (M₂ := (restrictOver R U).obj (unit _)) fun W ↦ ?_
    ext ψ
    let T' : (Over W.unop.left)ᵒᵖ := op (Over.mk (𝟙 W.unop.left))
    let b : ι → R.obj (op W.unop.left) := fun i ↦ ψ.app T' (A.map W.unop.hom.op (m i))
    -- `ψ` is a combination of the restrictions of the `c i`.
    have hψ : ψ = ∑ i, b i • (show (homObj A (unit _)).obj (op W.unop.left) from
        (homObj A (unit _)).map W.unop.hom.op (c i)) := by
      refine hom_ext (M₁ := (restrictOver R W.unop.left).obj A)
        (M₂ := (restrictOver R W.unop.left).obj (unit _)) fun W' ↦ ?_
      ext y
      let W'' : (Over U)ᵒᵖ := op ((Over.map W.unop.hom).obj W'.unop)
      refine (congrArg (ψ.app W') (hspan W'' y)).trans ?_
      refine (map_sum (ψ.app W').hom _ _).trans ?_
      refine Eq.trans ?_ (sum_app_apply _ _ W' y).symm
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hn : ψ.app W' (A.map W''.unop.hom.op (m i)) = R.map W'.unop.hom.op (b i) := by
        refine (congrArg (ψ.app W') (A.map_comp_apply W.unop.hom.op W'.unop.hom.op (m i))).trans ?_
        exact naturality_apply ψ
          (Over.homMk W'.unop.hom (Category.comp_id _) : W'.unop ⟶ Over.mk (𝟙 W.unop.left)).op _
      refine ((ψ.app W').hom.map_smul _ _).trans ?_
      refine Eq.trans ?_ (restrictOver_smul_app_apply (b i) _ W' y).symm
      change (show R.obj (op W'.unop.left) from (c i).app W'' y) *
          (show R.obj (op W'.unop.left) from ψ.app W' (A.map W''.unop.hom.op (m i))) =
        R.map W'.unop.hom.op (b i) * (show R.obj (op W'.unop.left) from (c i).app W'' y)
      dsimp only
      rw [hn]
      exact mul_comm _ _
    -- The value of `Ψ` at a restriction of `c i` is the restriction of `a i`.
    have hΨ (i : ι) : Ψ.app W ((homObj A (unit _)).map W.unop.hom.op (c i)) =
        R.map W.unop.hom.op (a i) :=
      naturality_apply Ψ
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op (c i)
    have hL : ((bidual A).app (op U) (∑ i, a i • m i)).app W ψ =
        ∑ i, R.map W.unop.hom.op (a i) * b i := by
      change ψ.app T' (A.map W.unop.hom.op (∑ i, a i • m i)) = _
      refine (congrArg (fun y : A.obj (op W.unop.left) ↦ ψ.app T' y)
        (map_sum (A.map W.unop.hom.op).hom _ _)).trans ?_
      refine (map_sum (ψ.app T').hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
      refine (congrArg (fun y : A.obj (op W.unop.left) ↦ ψ.app T' y)
        (A.map_smul W.unop.hom.op (a i) (m i))).trans ?_
      exact (ψ.app T').hom.map_smul _ _
    have hR : Ψ.app W ψ = ∑ i, b i * R.map W.unop.hom.op (a i) := by
      refine (congrArg (Ψ.app W) hψ).trans ?_
      refine (map_sum (Ψ.app W).hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
      exact ((Ψ.app W).hom.map_smul _ _).trans (congrArg (b i * ·) (hΨ i))
    rw [hL, hR]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm (R.map W.unop.hom.op (a i)) (b i)

/-- The restriction of a morphism between restrictions to `Over U` along `g : V ⟶ U` is additive
in the morphism. -/
lemma restrictOverMap_sum {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {V : C} (g : V ⟶ U)
    {ι : Type*} (t : Finset ι) (f : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj N)) :
    restrictOverMap g (∑ i ∈ t, f i) = ∑ i ∈ t, restrictOverMap g (f i) :=
  map_sum ({ toFun := restrictOverMap g, map_zero' := rfl, map_add' _ _ := rfl } :
    ((restrictOver R U).obj M ⟶ (restrictOver R U).obj N) →+
      ((restrictOver R V).obj M ⟶ (restrictOver R V).obj N)) f t

/-- **Biduality for locally free presheaves of modules of finite rank.** If `A` is free of
finite rank on `U`, then the biduality morphism is bijective on sections over every `V ⟶ U`. -/
lemma bidual_app_bijective_of_hom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj A))
    (c : ι → ((restrictOver R U).obj A ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) {V : C} (g : V ⟶ U) :
    Function.Bijective ((bidual A).app (op V)) := by
  refine bidual_app_bijective (fun i ↦ restrictOverMap g (s i)) (fun i ↦ restrictOverMap g (c i))
    (fun i j ↦ ?_) ?_
  · change restrictOverMap g (s j ≫ c i) = _
    rw [hsc]
    split_ifs
    · exact restrictOverMap_id (R := R) (M := unit _) (N := unit _) (𝟙 _)
    · rfl
  · change ∑ i, restrictOverMap g (c i ≫ s i) = _
    rw [← restrictOverMap_sum, htot]
    rfl

end PresheafOfModules
