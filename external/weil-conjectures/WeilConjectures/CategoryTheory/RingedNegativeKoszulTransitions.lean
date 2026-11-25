/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel

/-! # Explicit transitions for the ordered negative Koszul complex

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, the negative finite free Koszul system.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- The negative-factor transition has components (b,1) in degrees (-1,0).
Source: Stacks, Tag 0A0E
(auxiliary; not a blueprint node). -/
def ringedNegativeKoszulFactorTransitionF
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n : ℤ) :
    (ringedNegativeKoszulFactor O b (m + 1)).X n ⟶
      (ringedNegativeKoszulFactor O b m).X n :=
  if h : n = -1 then
    eqToHom (congrArg (ringedNegativeKoszulFactor O b (m + 1)).X h) ≫
      (HomologicalComplex.doubleXIso₀ _ _).hom ≫ (ringedKoszulScalar O b).asHom ≫
      (HomologicalComplex.doubleXIso₀ _ _).inv ≫
      eqToHom (congrArg (ringedNegativeKoszulFactor O b m).X h.symm)
  else if h : n = 0 then
    eqToHom (congrArg (ringedNegativeKoszulFactor O b (m + 1)).X h) ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
      eqToHom (congrArg (ringedNegativeKoszulFactor O b m).X h.symm)
  else 0

/-- The only nonzero chain square is b times b^(m+1) = b^(m+2).
Source: Stacks, Tag 0A0E
(auxiliary; not a blueprint node).
Proof: in degree -1 use the power identity; outside that degree both differentials
vanish by the two-term support. No scalar is inverted. -/
theorem ringedNegativeKoszulFactorTransitionF_comm
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n k : ℤ)
    (h : (ComplexShape.up ℤ).Rel n k) :
    ringedNegativeKoszulFactorTransitionF O b m n ≫
        (ringedNegativeKoszulFactor O b m).d n k =
      (ringedNegativeKoszulFactor O b (m + 1)).d n k ≫
        ringedNegativeKoszulFactorTransitionF O b m k := by
  have hk : n + 1 = k := h
  subst k
  by_cases hn : n = -1
  · subst n
    simp [ringedNegativeKoszulFactorTransitionF, ringedNegativeKoszulFactor,
      HomologicalComplex.double_d, Category.assoc, pow_succ, End.mul_asHom]
  · rw [show (ringedNegativeKoszulFactor O b m).d n (n + 1) = 0 from
      HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hn,
      show (ringedNegativeKoszulFactor O b (m + 1)).d n (n + 1) = 0 from
      HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hn]
    simp

/-- The actual chain map (b,1), with no choice of a transition.
Source: Stacks, Tag 0A0E
(auxiliary; not a blueprint node). -/
def ringedNegativeKoszulFactorTransition
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedNegativeKoszulFactor O b (m + 1) ⟶ ringedNegativeKoszulFactor O b m where
  f := ringedNegativeKoszulFactorTransitionF O b m
  comm' := ringedNegativeKoszulFactorTransitionF_comm O b m

/-- Tensor the explicit negative-factor transitions in their original order.
Source: Stacks, Tag 0A0E
(auxiliary; not a blueprint node). -/
def ringedNegativeKoszulTransition : (r : ℕ) →
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) → (m : ℕ) →
      ringedNegativeKoszul O r b (m + 1) ⟶ ringedNegativeKoszul O r b m :=
  fun r ↦ Nat.rec
    (fun _ _ ↦ 𝟙 _)
    (fun _ ih b m ↦
      ((ringedKoszulTensor O).map
        (ringedNegativeKoszulFactorTransition O (b 0) m)).app _ ≫
      ((ringedKoszulTensor O).obj _).map (ih (fun i ↦ b i.succ) m)) r

/-- The empty negative tensor is the dual of the empty positive tensor.
Source: Stacks, Tag 0A0E, the empty finite free complex
(auxiliary; not a blueprint node).
Proof: inverse Hom-unit evaluation identifies O[0] with Hom(O[0],O[0]).
Both transitions are identities. The positive projection is identity, so its
dual unit is this same inverse evaluation; the empty basis is the single unit. -/
theorem ringedNegativeKoszulZeroDuality
    (b : Fin 0 → (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : ∀ m : ℕ, ringedNegativeKoszul O 0 b m ≅
        (ringedKoszulDualTower O 0 b).obj (op m),
      (∀ m, ringedNegativeKoszulTransition O 0 b m ≫ (e m).hom =
        (e (m + 1)).hom ≫ (ringedKoszulDualTower O 0 b).map
          (homOfLE (Nat.le_succ m)).op) ∧
      (∀ m, ringedNegativeKoszulBasis O 0 b m ∅ 0 ≫ (e m).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O 0 b m).f 0) := by
  let e := (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).symm
  refine ⟨fun _ ↦ e, ?_, ?_⟩
  · intro m
    change 𝟙 _ ≫ e.hom = e.hom ≫
      ((homComplexFunctor (R := O)).flip.obj (ringedSiteRingComplex O)).map (𝟙 _)
    simp only [Category.id_comp, Functor.flip_obj_obj, Functor.flip_obj_map,
      Functor.map_id, NatTrans.id_app]
    exact (Category.comp_id e.hom).symm
  · intro m
    simp only [ringedNegativeKoszulBasis]
    change _ ≫ e.hom.f 0 = _ ≫
      (e.hom ≫ (((homComplexFunctor (R := O)).map (𝟙 _)).app _)).f 0
    simp only [Functor.comp_obj, Nat.zero_eq, Nat.succ_eq_add_one, Int.reduceNeg,
      Nat.rec_zero, ↓reduceDIte, eqToHom_refl, Category.comp_id, Functor.map_id,
      NatTrans.id_app, HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Iso.cancel_iso_inv_left]
    exact (Category.comp_id (e.hom.f 0)).symm

end CategoryTheory
