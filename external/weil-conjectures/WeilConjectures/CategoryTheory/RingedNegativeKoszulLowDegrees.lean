/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.SignedKoszulFiniteCoordinates

/-! # The two highest terms of an ordered negative Koszul tensor

Source: Stacks Project, algebraization.tex, lemma-derived-completion-koszul (0A0E),
the finite free complex in degrees -r through 0.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory

private def supportIso {E : Type*} [Category E] [Preadditive E]
    {I : Type} [Fintype I] (F : I → E) (p : I → Prop) [DecidablePred p]
    [HasBiproduct F] [HasBiproduct (Subtype.restrict p F)]
    (h : ∀ i, ¬ p i → IsZero (F i)) :
    (⨁ Subtype.restrict p F) ≅ ⨁ F where
  hom := biproduct.fromSubtype F p
  inv := biproduct.toSubtype F p
  hom_inv_id := biproduct.fromSubtype_toSubtype F p
  inv_hom_id := by
    rw [biproduct.toSubtype_fromSubtype]
    apply biproduct.hom_ext
    intro i
    rw [biproduct.map_π, Category.id_comp]
    by_cases hi : p i
    · simp only [hi, ↓reduceIte, Category.comp_id]
    · simp only [hi, ↓reduceIte, comp_zero]
      exact (h i hi).eq_of_tgt _ _

private theorem scalarPow_apply
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat).sections)
    (k : ℕ) (V : Cᵒᵖ) (x : O.obj.obj V) :
    ((ringedKoszulScalar O s) ^ k).asHom.val.app V x =
      x * (show O.obj.obj V from s.val V) ^ k := by
  induction k with
  | zero => change x = x * _ ^ 0; simp
  | succ k ih =>
    rw [pow_succ']
    change (ringedKoszulScalar O s).asHom.val.app V
      (((ringedKoszulScalar O s) ^ k).asHom.val.app V x) = _
    change (show O.obj.obj V from ((ringedKoszulScalar O s) ^ k).asHom.val.app V x) *
      (show O.obj.obj V from s.val V) = _
    rw [ih, pow_succ, mul_assoc]

/-- The last differential of a negative Koszul tensor is the row of generator powers.
This is a statement about two terms of one finite complex, with no quotient, tower,
coefficient-ring presentation, or augmentation.

Source: Stacks Project, algebraization.tex, lemma-derived-completion-koszul (0A0E),
the negative finite free Koszul complex; more-algebra.tex, lemma-sequence-Koszul-complexes.
(auxiliary; not a blueprint node).

Proof: expand the ordered tensor by its standard subset basis. In degree zero the
only subset is empty, so its inclusion ringedNegativeKoszulBasis is an isomorphism
from the rank-one module. In degree -1 precisely the singleton subsets survive,
so their pure-tensor inclusions give an isomorphism from the direct sum of r copies
of the rank-one module. The differential on the singleton {i} changes the ith
factor from degree -1 to degree zero and is multiplication by b_i^(m+1).
All earlier factors have degree zero, so the total-tensor sign is +1. Thus its
row in these coordinates is exactly the displayed power of ringedKoszulScalar.
For r=0 the degree -1 term and the empty biproduct are zero; the degree-zero
identification is the single-complex identification. The same basis calculation
works on empty sites, over the zero ring, and for zero or unit sections. -/
theorem ringedNegativeKoszulLowDegrees
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    let M := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let K := ringedNegativeKoszul O r b m
    ∃ (e₀ : K.X 0 ≅ M) (e₁ : (⨁ fun _ : Fin r ↦ M) ≅ K.X (-1)),
      e₀.inv = ringedNegativeKoszulBasis O r b m ∅ 0 ∧
      ∀ i : Fin r, biproduct.ι _ i ≫ e₁.hom ≫ K.d (-1) 0 ≫ e₀.hom =
        ((ringedKoszulScalar O (b i)) ^ (m + 1)).asHom := by
  classical
  let M := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let K := ringedSiteRingComplex O
  let Γ := RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat)
  let ρ : Γ →+* Γ := RingHom.id Γ
  let a : Fin r → Γ := fun i ↦ ⟨(b i).val, (b i).property⟩
  obtain ⟨c, _, _, hd, _, _, _, hc, _, _⟩ :=
    exists_ringedSignedKoszulFiniteCoordinates O ρ r a
  let N := ringedNegativeKoszul O r b m
  let := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let l : ((ringedNegativeKoszulTensor O ρ a m).obj K) ≅ N :=
    HomologicalComplex.leftUnitor N
  let c' (q : ℤ) :=
    (HomologicalComplex.eval _ (.up ℤ) q).mapIso l.symm ≪≫ c m K q
  let F (q : ℤ) (I : Finset (Fin r)) := K.X (q + I.card)
  let z₀ : (⨁ F 0) ≅ M :=
    { hom := biproduct.π (F 0) ∅ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom
      inv := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ biproduct.ι (F 0) ∅
      hom_inv_id := by
        apply biproduct.hom_ext'
        intro I
        by_cases hI : I = ∅
        · subst I; simp [F]
        · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M
            ((0 : ℤ) + I.card) (by simpa using hI)).eq_of_src
      inv_hom_id := by simp [F] }
  let z : N.X 0 ≅ M := c' 0 ≪≫ z₀
  let e : Fin r ≃ {I : Finset (Fin r) // I.card = 1} :=
    Equiv.ofBijective (fun i ↦ ⟨{i}, by simp⟩) ⟨
      fun i j h ↦ Finset.singleton_injective (congrArg Subtype.val h),
      fun I ↦ by
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp I.property
        exact ⟨i, Subtype.ext hi.symm⟩⟩
  let s₁ := supportIso (F (-1)) (fun I ↦ I.card = 1) (fun I hi ↦
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M _ (by
      omega))
  let t : (⨁ fun _ : Fin r ↦ M) ≅ N.X (-1) :=
    biproduct.whiskerEquiv e (fun i ↦
      HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M _ (by simp [e])) ≪≫
        s₁ ≪≫ (c' (-1)).symm
  refine ⟨z, t, ?_, ?_⟩
  · change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫
        biproduct.ι (F 0) ∅ ≫ (c m K 0).inv ≫ l.hom.f 0 = _
    rw [reassoc_of% (hc m K 0 ∅)]
    have hl : l.inv.f 0 = (MonoidalCategory.leftUnitor (N.X 0)).inv ≫
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ▷ N.X 0) ≫
          CochainComplex.ιMapBifunctor K N (MonoidalCategory.curriedTensor _)
            0 0 0 (by omega) := HomologicalComplex.leftUnitor'_inv N 0
    apply (cancel_mono (l.inv.f 0)).1
    simp only [Category.assoc, ← HomologicalComplex.comp_f,
      l.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]
    rw [hl]
    simp only [ringedNegativeKoszulSummand, Finset.card_empty, Int.natCast_zero,
      MonoidalCategory.id_tensorHom]
    change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫
        (MonoidalCategory.rightUnitor (K.X 0)).inv ≫
          (K.X 0) ◁ ringedNegativeKoszulBasis O r b m ∅ 0 ≫
            CochainComplex.ιMapBifunctor K N (MonoidalCategory.curriedTensor _)
              0 0 0 (by omega) =
      ringedNegativeKoszulBasis O r b m ∅ 0 ≫
        (MonoidalCategory.leftUnitor (N.X 0)).inv ≫
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ▷ N.X 0) ≫
            CochainComplex.ιMapBifunctor K N (MonoidalCategory.curriedTensor _)
              0 0 0 (by omega)
    rw [MonoidalCategory.rightUnitor_inv_naturality_assoc,
      ← MonoidalCategory.whisker_exchange_assoc,
      MonoidalCategory.leftUnitor_inv_naturality_assoc]
    have hu : (MonoidalCategory.leftUnitor M).inv =
        (MonoidalCategory.rightUnitor M).inv := MonoidalCategory.unitors_inv_equal
    rw [hu]
    rfl
  · intro i
    have hti : biproduct.ι _ i ≫ t.hom =
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M
          (-1 + (({i} : Finset (Fin r)).card : ℤ)) (by simp)).inv ≫
          biproduct.ι (F (-1)) {i} ≫ (c m K (-1)).inv ≫ l.hom.f (-1) := by
      simp [t, s₁, supportIso, c', e, Category.assoc,
        HomologicalComplex.singleObjXIsoOfEq]
    rw [reassoc_of% hti]
    change _ ≫ _ ≫ _ ≫ l.hom.f (-1) ≫ N.d (-1) 0 ≫
      l.inv.f 0 ≫ (c m K 0).hom ≫ biproduct.π _ ∅ ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = _
    rw [l.hom.comm_assoc]
    have hli : l.hom.f 0 ≫ l.inv.f 0 = 𝟙 _ :=
      congrArg (fun f ↦ f.f 0) l.hom_inv_id
    rw [reassoc_of% hli]
    have h : biproduct.ι (F (-1)) {i} ≫ (c m K (-1)).inv ≫
        ((ringedNegativeKoszulTensor O ρ a m).obj K).d (-1) 0 ≫
          (c m K 0).hom ≫ biproduct.π (F 0) ∅ =
        ringedKoszulCoefficientSMul O ρ (a i ^ (m + 1))
          (𝟙 (K.X (-1 + (({i} : Finset (Fin r)).card : ℤ)))) := by
      simpa [F, Finset.filter_singleton, Int.natCast_one] using hd m K (-1) {i} ∅
    rw [reassoc_of% h]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (show O.obj.obj V from (a i ^ (m + 1)).val V) * (show O.obj.obj V from x) =
      ((ringedKoszulScalar O (b i)) ^ (m + 1)).asHom.val.app V x
    rw [scalarPow_apply]
    exact mul_comm _ _

end CategoryTheory
