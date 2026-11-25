/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.RingTheory.FaithfullyFlat.FamilyDescent

/-!
# Exactness of Čech complexes by faithfully flat base change

Let `C` be a category, `V` an object of `C` and `U : ι → Over V` a finite family. Suppose that
the sections of a presheaf `P` of abelian groups over objects `W` of `Over V` are modules
`M(W)` over a ring `A`, and that for every member `U a` of the family, the base change
`M(W) ⊗_A B_a` is `M(W ×_V U a)` for a module `B_a`, naturally in `W`. If `⨁ₐ B_a` is faithfully
flat over `A`, then the Čech complex of `P` on the family `U` is exact in positive degrees.

Indeed, after tensoring with `B_a` the Čech complex becomes the complex
`k ↦ ∏_y M(U (y 0) ×_V ⋯ ×_V U (y k) ×_V U a)`, which is contracted by the homotopy inserting
`U a` in front of a tuple (via the diagonal of `U a`). Faithful flatness reflects exactness.

This is the argument for the étale acyclicity of quasi-coherent sheaves on affine schemes
(Stacks `03OW`), applied to `B_a = Γ(U a, 𝒪)`.

## Main statements

- `CategoryTheory.Presheaf.exists_baseChangeCech_eq`: the base changed Čech complex
  `k ↦ ∏_y Q(U (y 0) ×_V ⋯ ×_V U (y k) ×_V U a)` of any presheaf `Q` on `Over V` is exact in
  positive degrees.
- `CategoryTheory.Presheaf.exactAt_cechComplex_of_baseChange`: the exactness criterion.
-/

@[expose] public section

universe s t v w

open CategoryTheory Limits Opposite TensorProduct

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] {ι : Type t}
  (U : ι → Over V)

section BaseChange

variable (a : ι) (Q : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{s})

/-- The member `U (y 0) ×_V ⋯ ×_V U (y k) ×_V U a` of the base change of the Čech nerve of `U`
along `U a ⟶ V`. -/
noncomputable abbrev bcNerveObj {k : ℕ} (y : Fin (k + 1) → ι) : Over V :=
  cechNerveObj U y ⨯ U a

/-- The maps of the base changed Čech nerve. -/
noncomputable abbrev bcNerveMap {k m : ℕ} (y : Fin (m + 1) → ι)
    (θ : Fin (k + 1) → Fin (m + 1)) : bcNerveObj U a y ⟶ bcNerveObj U a (y ∘ θ) :=
  prod.map (cechNerveMap U y θ) (𝟙 _)

/-- The differential of the base changed Čech complex of `Q`. -/
noncomputable def bcD (k : ℕ) (x : ∀ y : Fin (k + 1) → ι, Q.obj (op (bcNerveObj U a y)))
    (y : Fin (k + 2) → ι) : Q.obj (op (bcNerveObj U a y)) :=
  ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
    Q.map (bcNerveMap U a y i.succAbove).op (x (y ∘ i.succAbove))

/-- The section `U (y 0) ×_V ⋯ ×_V U (y k) ×_V U a ⟶ U a ×_V U (y 0) ×_V ⋯ ×_V U (y k) ×_V U a`
given by the diagonal of `U a`. -/
noncomputable abbrev bcCons {k : ℕ} (y : Fin (k + 1) → ι) :
    bcNerveObj U a y ⟶ bcNerveObj U a (Fin.cons a y : Fin (k + 2) → ι) :=
  prod.lift (cechNerveCons U prod.snd prod.fst) prod.snd

lemma bc_cochain_congr {k : ℕ} (x : ∀ y : Fin (k + 1) → ι, Q.obj (op (bcNerveObj U a y)))
    {y y' : Fin (k + 1) → ι} (h : y = y') {W : Over V} (G : W ⟶ bcNerveObj U a y)
    (G' : W ⟶ bcNerveObj U a y')
    (hG : G ≫ eqToHom (congrArg (fun y ↦ bcNerveObj U a y) h) = G') :
    Q.map G.op (x y) = Q.map G'.op (x y') := by
  subst h hG
  simp

/-- A component of a base changed Čech cochain along a face, after transport along an equality
of tuples. -/
lemma bc_cochain_face_eq {k m : ℕ}
    (x : ∀ y : Fin (k + 1) → ι, Q.obj (op (bcNerveObj U a y))) {W : Over V}
    {y : Fin (m + 1) → ι} (G : W ⟶ bcNerveObj U a y)
    (θ : Fin (k + 1) → Fin (m + 1)) {y' : Fin (k + 1) → ι} (h : y ∘ θ = y')
    (G' : W ⟶ bcNerveObj U a y')
    (hG : ∀ l, G ≫ prod.fst ≫ Pi.π _ (θ l) ≫ eqToHom (congrArg U (congrFun h l)) =
      G' ≫ prod.fst ≫ Pi.π _ l)
    (hG' : G ≫ prod.snd = G' ≫ prod.snd) :
    Q.map (G ≫ bcNerveMap U a y θ).op (x (y ∘ θ)) = Q.map G'.op (x y') := by
  refine bc_cochain_congr U a Q x h _ _ ?_
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  refine prod.hom_ext ?_ ?_
  · refine Pi.hom_ext _ _ fun l ↦ ?_
    have h := hG l
    simp only [eqToHom_refl, Category.comp_id] at h
    simp only [Category.assoc, prod.map_fst_assoc]
    erw [cechNerveMap_π]
    exact h
  · simp [hG']

/-- **The base changed Čech complex is exact.** For every presheaf `Q` on `Over V`, the complex
`k ↦ ∏_y Q(U (y 0) ×_V ⋯ ×_V U (y k) ×_V U a)` is exact in positive degrees: it is contracted by
the homotopy `x ↦ (y ↦ x (a, y))` restricted along the diagonal of `U a`. -/
theorem exists_bcD_eq (q : ℕ) (x : ∀ y : Fin (q + 2) → ι, Q.obj (op (bcNerveObj U a y)))
    (hx : bcD U a Q (q + 1) x = 0) :
    ∃ z : ∀ y : Fin (q + 1) → ι, Q.obj (op (bcNerveObj U a y)), bcD U a Q q z = x := by
  refine ⟨fun y ↦ Q.map (bcCons U a y).op (x (Fin.cons a y)), ?_⟩
  funext y
  have h₀ := congrArg (Q.map (bcCons U a y).op) (congrFun hx (Fin.cons a y))
  rw [bcD, map_sum, Fin.sum_univ_succ] at h₀
  simp only [map_zsmul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at h₀
  change _ = Q.map (bcCons U a y).op 0 at h₀
  rw [map_zero] at h₀
  -- the first face is `x y`
  have e₀ : Q.map (bcCons U a y ≫ bcNerveMap U a (Fin.cons a y : Fin (q + 3) → ι)
      (0 : Fin (q + 3)).succAbove).op (x ((Fin.cons a y : Fin (q + 3) → ι) ∘
        (0 : Fin (q + 3)).succAbove)) = x y :=
    (bc_cochain_face_eq U a Q x _ _ (by funext l; simp) (𝟙 _) (fun l ↦ by
      simp only [Category.id_comp]
      rw [prod.lift_fst_assoc]
      exact cechNerveCons_π_of_eq_succ U _ _ _ l (by simp) _) (by simp)).trans (by simp)
  -- the other faces are the terms of the differential of the homotopy
  have e (i : Fin (q + 2)) : Q.map (bcCons U a y ≫ bcNerveMap U a (Fin.cons a y : Fin (q + 3) → ι)
      i.succ.succAbove).op (x ((Fin.cons a y : Fin (q + 3) → ι) ∘ i.succ.succAbove)) =
      Q.map (bcNerveMap U a y i.succAbove).op
        (Q.map (bcCons U a (y ∘ i.succAbove)).op (x (Fin.cons a (y ∘ i.succAbove)))) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    refine bc_cochain_face_eq U a Q x _ _
      (by funext l; cases l using Fin.cases with | zero => rfl | succ l => simp) _
      (fun l ↦ ?_) (by simp)
    cases l using Fin.cases with
    | zero =>
      rw [prod.lift_fst_assoc, cechNerveCons_π_of_eq_zero U _ _ _ (by simp) _]
      simp only [Category.assoc, prod.lift_fst_assoc]
      erw [cechNerveCons_π_zero]
      exact ((prod.map_snd _ _).trans (Category.comp_id _)).symm
    | succ l =>
      rw [prod.lift_fst_assoc, cechNerveCons_π_of_eq_succ U _ _ _ (i.succAbove l) (by simp) _]
      simp only [Category.assoc, prod.lift_fst_assoc]
      erw [cechNerveCons_π_succ]
      simp only [prod.map_fst_assoc]
      erw [cechNerveMap_π]
  rw [e₀] at h₀
  simp only [e, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    Fin.val_zero, pow_zero, one_smul] at h₀
  rw [bcD]
  exact (add_neg_eq_zero.mp h₀).symm

end BaseChange

end CategoryTheory.Presheaf

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] {ι : Type t}
  (U : ι → Over V)

section Criterion

lemma bcD_zero (a : ι) (Q : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{s}) (k : ℕ) :
    bcD U a Q k 0 = 0 := by
  funext y
  simp [bcD]

lemma bcD_add (a : ι) (Q : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{s}) (k : ℕ)
    (x x' : ∀ y : Fin (k + 1) → ι, Q.obj (op (bcNerveObj U a y))) :
    bcD U a Q k (x + x') = bcD U a Q k x + bcD U a Q k x' := by
  funext y
  simp [bcD, Finset.sum_add_distrib]

variable {A : Type*} [CommRing A] (M : (Over V)ᵒᵖ ⥤ ModuleCat.{s} A)

/-- The Čech cochains of degree `k` of a presheaf of `A`-modules on `Over V`. -/
abbrev ModuleCechCochain (k : ℕ) : Type _ :=
  ∀ y : Fin (k + 1) → ι, M.obj (op (cechNerveObj U y))

/-- The Čech differential of a presheaf of `A`-modules on `Over V`, as an `A`-linear map. -/
noncomputable def moduleCechD (k : ℕ) :
    ModuleCechCochain U M k →ₗ[A] ModuleCechCochain U M (k + 1) :=
  LinearMap.pi fun y ↦ ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
    ((M.map (cechNerveMap U y i.succAbove).op).hom ∘ₗ LinearMap.proj (y ∘ i.succAbove))

lemma moduleCechD_apply (k : ℕ) (c : ModuleCechCochain U M k) (y : Fin (k + 2) → ι) :
    moduleCechD U M k c y = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      M.map (cechNerveMap U y i.succAbove).op (c (y ∘ i.succAbove)) := by
  simp [moduleCechD]

variable {U M}

lemma moduleCechD_comp_eq_zero (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (φ : ∀ {k : ℕ} (y : Fin (k + 1) → ι),
      P.obj (op (cechNerveObj U y).left) ≃+ M.obj (op (cechNerveObj U y)))
    (hφ : ∀ {k m : ℕ} (y : Fin (m + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1))
      (s : P.obj (op (cechNerveObj U (y ∘ θ)).left)),
      φ y (P.map (cechNerveMap U y θ).left.op s) =
        M.map (cechNerveMap U y θ).op (φ (y ∘ θ) s)) (k : ℕ) :
    moduleCechD U M (k + 1) ∘ₗ moduleCechD U M k = 0 := by
  -- the Čech complexes of `P` and `M` are identified by `φ`
  have key (k : ℕ) (c : ((cechComplex U).obj P).X k) :
      moduleCechD U M k (fun y ↦ φ _ (c y)) =
        fun y ↦ φ _ (((cechComplex U).obj P).d k (k + 1) c y) := by
    funext y
    rw [moduleCechD_apply, cechComplex_d_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, hφ y i.succAbove]
  ext c : 1
  let c' : ((cechComplex U).obj P).X k := fun y ↦ (φ _).symm (c y)
  have hc : c = fun y ↦ φ _ (c' y) := by
    funext y
    simp [c']
  rw [LinearMap.comp_apply, hc, key, key, cechComplex_d_d_apply]
  funext y
  simp

/-- The `y`-component of an element of `(∏_y M_y) ⊗ N`. -/
lemma piLeft_apply_eq_rTensor_proj {κ : Type*} [Fintype κ] [DecidableEq κ] {R : Type*}
    [CommRing R] {Mₖ : κ → Type*} [∀ i, AddCommGroup (Mₖ i)] [∀ i, Module R (Mₖ i)] {N : Type*}
    [AddCommGroup N] [Module R N] (t : (∀ i, Mₖ i) ⊗[R] N) (i : κ) :
    TensorProduct.piLeft R N Mₖ t i = (LinearMap.proj i).rTensor N t := by
  induction t using TensorProduct.inductionOn with
  | tmul x n => simp
  | add x x' hx hx' => simp only [map_add, Pi.add_apply, hx, hx']

variable (U M) in
/-- **Exactness of Čech complexes by faithfully flat base change.** Let `P` be a presheaf of
abelian groups on `C` whose sections over the objects `W` of `Over V` are the `A`-modules
`M(W)`, compatibly with restrictions. Let `B_a`, for `a ∈ ι` finite, be `A`-modules with
`∏ₐ B_a` faithfully flat over `A`, together with maps `M(W) ⊗_A B_a → M(W ×_V U a)`, natural in
`W` and bijective on the members of the Čech nerve of `U`. Then the Čech complex of `P` on the
family `U` is exact in positive degrees. -/
theorem exactAt_cechComplex_of_baseChange [Finite ι] (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (φ : ∀ {k : ℕ} (y : Fin (k + 1) → ι),
      P.obj (op (cechNerveObj U y).left) ≃+ M.obj (op (cechNerveObj U y)))
    (hφ : ∀ {k m : ℕ} (y : Fin (m + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1))
      (s : P.obj (op (cechNerveObj U (y ∘ θ)).left)),
      φ y (P.map (cechNerveMap U y θ).left.op s) =
        M.map (cechNerveMap U y θ).op (φ (y ∘ θ) s))
    (B : ι → Type*) [∀ a, AddCommGroup (B a)] [∀ a, Module A (B a)]
    [Module.FaithfullyFlat A (∀ a, B a)]
    (e : ∀ (a : ι) (W : Over V), M.obj (op W) ⊗[A] B a →+ M.obj (op (W ⨯ U a)))
    (he : ∀ (a : ι) {W W' : Over V} (f : W ⟶ W') (s : M.obj (op W')) (b : B a),
      e a W (M.map f.op s ⊗ₜ b) = M.map (prod.map f (𝟙 (U a))).op (e a W' (s ⊗ₜ b)))
    (hbij : ∀ (a : ι) {k : ℕ} (y : Fin (k + 1) → ι),
      Function.Bijective (e a (cechNerveObj U y)))
    (q : ℕ) : ((cechComplex U).obj P).ExactAt (q + 1) := by
  classical
  have := Fintype.ofFinite ι
  set d := moduleCechD U M
  have hdd (k : ℕ) := moduleCechD_comp_eq_zero (U := U) P φ hφ k
  -- exactness after base change to each `B a`
  have hexa (a : ι) : Function.Exact ((d q).rTensor (B a)) ((d (q + 1)).rTensor (B a)) := by
    let Q := M ⋙ forget₂ (ModuleCat A) AddCommGrpCat
    let E (k : ℕ) (t : ModuleCechCochain U M k ⊗[A] B a) :
        ∀ y : Fin (k + 1) → ι, Q.obj (op (bcNerveObj U a y)) :=
      fun y ↦ e a _ ((LinearMap.proj y).rTensor (B a) t)
    have hE (k : ℕ) : Function.Bijective (E k) := by
      have h₁ := (TensorProduct.piLeft A (B a) (fun y : Fin (k + 1) → ι ↦
        M.obj (op (cechNerveObj U y)))).bijective
      have h₂ : Function.Bijective (fun (g : ∀ y : Fin (k + 1) → ι,
          M.obj (op (cechNerveObj U y)) ⊗[A] B a) (y : Fin (k + 1) → ι) ↦ e a _ (g y)) :=
        Function.Bijective.piMap fun y ↦ hbij a y
      have heq : E k = (fun (g : ∀ y : Fin (k + 1) → ι,
          M.obj (op (cechNerveObj U y)) ⊗[A] B a) (y : Fin (k + 1) → ι) ↦ e a _ (g y)) ∘
          (TensorProduct.piLeft A (B a) (fun y : Fin (k + 1) → ι ↦
            M.obj (op (cechNerveObj U y)))) := by
        funext t y
        simp only [Function.comp_apply, piLeft_apply_eq_rTensor_proj]
        rfl
      rw [heq]
      exact h₂.comp h₁
    have hEadd (k : ℕ) (t t' : ModuleCechCochain U M k ⊗[A] B a) :
        E k (t + t') = E k t + E k t' := funext fun y ↦ by simp [E]
    have hEd (k : ℕ) (t : ModuleCechCochain U M k ⊗[A] B a) :
        E (k + 1) ((d k).rTensor (B a) t) = bcD U a Q k (E k t) := by
      induction t using TensorProduct.inductionOn with
      | add x x' hx hx' =>
        rw [map_add, hEadd, hx, hx', hEadd, bcD_add]
      | tmul c b =>
        funext y
        simp only [E, LinearMap.rTensor_tmul, LinearMap.coe_proj, Function.eval]
        rw [moduleCechD_apply, TensorProduct.sum_tmul, map_sum, bcD]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← TensorProduct.smul_tmul', map_zsmul, he]
        rfl
    refine LinearMap.exact_iff.2 (le_antisymm (fun t ht ↦ ?_) ?_)
    · rw [LinearMap.mem_ker] at ht
      have h0 : bcD U a Q (q + 1) (E (q + 1) t) = 0 := by
        rw [← hEd, ht]
        funext y
        simp [E]
      obtain ⟨z, hz⟩ := exists_bcD_eq U a Q q _ h0
      obtain ⟨t', rfl⟩ := (hE q).2 z
      exact ⟨t', (hE (q + 1)).1 (by rw [hEd, hz])⟩
    · rintro _ ⟨t, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hdd,
        LinearMap.rTensor_zero, LinearMap.zero_apply]
  -- exactness after base change to `∏ₐ B a`, hence before base change
  have hex : Function.Exact (d q) (d (q + 1)) := by
    rw [← Module.FaithfullyFlat.rTensor_exact_iff_exact A (∀ a, B a)]
    have hcomm (k : ℕ) (t : ModuleCechCochain U M k ⊗[A] (∀ a, B a)) (a : ι) :
        TensorProduct.piRight A A _ B ((d k).rTensor _ t) a =
          (d k).rTensor (B a) (TensorProduct.piRight A A _ B t a) := by
      rw [TensorProduct.piRight_apply_eq_lTensor_proj, TensorProduct.piRight_apply_eq_lTensor_proj,
        ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    refine LinearMap.exact_iff.2 (le_antisymm (fun t ht ↦ ?_) ?_)
    · rw [LinearMap.mem_ker] at ht
      have ha (a : ι) :=
        (LinearMap.exact_iff.1 (hexa a)).le (x := TensorProduct.piRight A A _ B t a)
          (by rw [LinearMap.mem_ker, ← hcomm, ht, map_zero, Pi.zero_apply])
      choose s hs using ha
      refine ⟨(TensorProduct.piRight A A _ B).symm s, (TensorProduct.piRight A A _ B).injective ?_⟩
      funext a
      rw [hcomm, LinearEquiv.apply_symm_apply, hs]
    · rintro _ ⟨t, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hdd,
        LinearMap.rTensor_zero, LinearMap.zero_apply]
  -- transport to the Čech complex of `P`
  have key (k : ℕ) (c : ((cechComplex U).obj P).X k) :
      d k (fun y ↦ φ _ (c y)) = fun y ↦ φ _ (((cechComplex U).obj P).d k (k + 1) c y) := by
    funext y
    rw [moduleCechD_apply, cechComplex_d_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, hφ y i.succAbove]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨m, hm⟩ := (LinearMap.exact_iff.1 hex).le (x := fun y ↦ φ _ (c y)) (by
    rw [LinearMap.mem_ker, key, hc]
    funext y
    simp)
  refine ⟨fun y ↦ (φ _).symm (m y), funext fun y ↦ (φ _).injective ?_⟩
  have := congrFun (key q fun y ↦ (φ _).symm (m y)) y
  simp only [AddEquiv.apply_symm_apply] at this
  rw [← this]
  exact congrFun hm y

end Criterion

end CategoryTheory.Presheaf
