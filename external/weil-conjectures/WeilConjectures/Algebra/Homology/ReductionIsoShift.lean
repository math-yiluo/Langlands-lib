/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison

/-! # The canonical principal reduction comparison and shifts -/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type r} [CommRing B] [Linear B A] [MonoidalLinear B A]

local instance instHasColimitsOfSizeReductionIsoShift :
    HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

open CochainComplex HomComplex mappingCone HomologicalComplex

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private lemma inv_inl (M : CochainComplex A ℤ) (b : B) (i n : ℤ)
    (hi : i = n + 1) :
    (inl (b • 𝟙 M)).v i n (by omega) ≫ (tensorScalarConeIso' M b).inv.f n =
      (ρ_ M).inv.f i ≫
        (mapBifunctorMappingCone₂Iso.ι₁ M
          ((single A (.up ℤ) 0).map (b • 𝟙 (𝟙_ A))) (curriedTensor A)).v
          i n (by omega) := by
  subst i
  simp [tensorScalarConeIso', mappingCone.map, mapBifunctorMappingCone₂Iso.inv,
    Cochain.comp_v _ _ (zero_add (-1)) (n + 1) (n + 1) n (by omega) (by omega)]

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private lemma inv_inr (M : CochainComplex A ℤ) (b : B) :
    inr (b • 𝟙 M) ≫ (tensorScalarConeIso' M b).inv =
      (ρ_ M).inv ≫ M ◁ inr ((single A (.up ℤ) 0).map (b • 𝟙 (𝟙_ A))) := by
  rw [← cancel_mono (tensorScalarConeIso' M b).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (inr_tensorScalarConeIso'_hom M b).symm

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [MonoidalLinear B A] in
private lemma iota_shift (M : CochainComplex A ℤ) (b : B) (t n : ℤ) :
    (mapBifunctorMappingCone₂Iso.ι₁ (M⟦t⟧)
        ((single A (.up ℤ) 0).map (b • 𝟙 (𝟙_ A))) (curriedTensor A)).v
        (n + 1) n (by omega) ≫
      (mapBifunctorShift₁Iso M (scalarCone b) (curriedTensor A) t).hom.f n =
    t.negOnePow •
      ((mapBifunctorShift₁Iso M (𝟙_ (CochainComplex A ℤ))
          (curriedTensor A) t).hom.f (n + 1) ≫
        (mapBifunctorMappingCone₂Iso.ι₁ M
          ((single A (.up ℤ) 0).map (b • 𝟙 (𝟙_ A))) (curriedTensor A)).v
          (n + 1 + t) (n + t) (by omega)) := by
  ext p q hpq
  simp only [Linear.comp_units_smul]
  erw [mapBifunctorMappingCone₂Iso.ι_ι₁_assoc _ _ _ p q (n + 1) hpq
    n (by omega) (q - 1) (by omega)]
  simp only [Linear.units_smul_comp, Category.assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f M (scalarCone b) (curriedTensor A) t
    p (q - 1) n (by dsimp at hpq ⊢; omega) (p + t) (n + t) rfl rfl]
  erw [ι_mapBifunctorShift₁Iso_hom_f_assoc M (𝟙_ (CochainComplex A ℤ))
    (curriedTensor A) t p q (n + 1) hpq (p + t) (n + 1 + t) rfl rfl]
  simp only [shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    curriedTensor_map_app, Category.id_comp,
    Category.comp_id]
  erw [mapBifunctorMappingCone₂Iso.ι_ι₁ _ _ _ (p + t) q (n + 1 + t)
    (by dsimp at hpq ⊢; omega) (n + t) (by omega) (q - 1) (by omega)]
  erw [MonoidalCategory.id_whiskerRight, MonoidalCategory.id_whiskerRight]
  simp only [shiftFunctor_obj_X', curriedTensor_obj_obj, Int.reduceNeg,
    curriedTensor_obj_map, Category.id_comp, Linear.comp_units_smul,
    Int.negOnePow_add, smul_smul]
  rw [mul_comm p.negOnePow t.negOnePow, ← mul_assoc, Int.units_mul_self, one_mul]
  erw [Category.id_comp]

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private lemma chain_inv_shift (M : CochainComplex A ℤ) (b : B) (t : ℤ) :
    (mappingCone.shiftIso (b • 𝟙 M) t).inv ≫ (tensorScalarConeIso' M b).inv⟦t⟧' =
      (tensorScalarConeIso' (M⟦t⟧) b).inv ≫
        (mapBifunctorShift₁Iso M (scalarCone b) (curriedTensor A) t).hom := by
  ext n
  apply mappingCone.ext_from (b • 𝟙 (M⟦t⟧)) (n + 1) n rfl
  · simp only [HomologicalComplex.comp_f, mappingCone.shiftIso, shiftFunctor_map_f']
    erw [inl_v_desc_f_assoc]
    simp only [Cochain.units_smul_v, Cochain.shift_v', Linear.units_smul_comp]
    erw [inv_inl M b (n + 1 + t) (n + t) (by omega),
      ← Category.assoc, inv_inl (M⟦t⟧) b (n + 1) n rfl]
    simp only [Category.assoc]
    erw [iota_shift]
    simp only [Linear.comp_units_smul, ← Category.assoc]
    have hu := congrArg (fun f ↦ f.f (n + 1))
      (rightUnitor_inv_mapBifunctorShift₁Iso_hom M t)
    dsimp only [HomologicalComplex.comp_f, shiftFunctor_map_f'] at hu
    erw [hu]
  · simp only [HomologicalComplex.comp_f, mappingCone.shiftIso, shiftFunctor_map_f']
    have hi := congrArg (fun f ↦ f.f (n + t)) (inv_inr M b)
    have hj := congrArg (fun f ↦ f.f n) (inv_inr (M⟦t⟧) b)
    dsimp only [HomologicalComplex.comp_f] at hi hj
    erw [inr_f_desc_f_assoc]
    simp only [shiftFunctor_map_f']
    rw [hi, ← Category.assoc, hj, Category.assoc]
    have hs := NatTrans.shift_app_comm
      ((curriedTensor A).map₂CochainComplex.flip.map
        (inr ((single A (.up ℤ) 0).map (b • 𝟙 (𝟙_ A))))) t M
    simp only [Functor.commShiftIso_map₂CochainComplex_flip_hom_app] at hs
    have hh := congrArg (fun f ↦ f.f n) hs
    dsimp only [HomologicalComplex.comp_f, shiftFunctor_map_f'] at hh
    erw [← hh, ← Category.assoc]
    have hu := congrArg (fun f ↦ f.f n)
      (rightUnitor_inv_mapBifunctorShift₁Iso_hom M t)
    dsimp only [HomologicalComplex.comp_f, shiftFunctor_map_f'] at hu
    erw [hu]
    rfl

private lemma mu_shift (M K : CochainComplex A ℤ) (t : ℤ)
    (hK : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
      ((HomotopyCategory.quotient A (.up ℤ)).obj K)) :
    Functor.LaxMonoidal.μ Q (M⟦t⟧) K ≫
        Q.map (mapBifunctorShift₁Iso M K (curriedTensor A) t).hom ≫
        (Q.commShiftIso t).hom.app (M ⊗ K) =
      (tensorRight (Q.obj K)).map ((Q.commShiftIso t).hom.app M) ≫
        ((tensorRight (Q.obj K)).commShiftIso t).hom.app (Q.obj M) ≫
        (Functor.LaxMonoidal.μ Q M K)⟦t⟧' := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let e := quotientCompQhIso A
  let f := (curriedTensor A).quotientCompBifunctorMapHomotopyFlipObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) K
  let a : Q ⋙ tensorRight (Q.obj K) ⟶
      q ⋙ (Qh ⋙ tensorRight (Qh.obj (q.obj K))) :=
    Functor.whiskerRight e.inv (tensorRight (Q.obj K)) ≫
      Functor.whiskerLeft (q ⋙ Qh) ((curriedTensor _).flip.map (e.inv.app K)) ≫
      (Functor.associator q Qh (tensorRight (Qh.obj (q.obj K)))).hom
  let c : q ⋙ (tensorRight (q.obj K) ⋙ Qh) ⟶ tensorRight K ⋙ Q :=
    (Functor.associator q (tensorRight (q.obj K)) Qh).inv ≫
      Functor.whiskerRight f.hom Qh ≫
      (Functor.associator (tensorRight K) q Qh).hom ≫
      Functor.whiskerLeft (tensorRight K) e.hom
  let τ : Q ⋙ tensorRight (Q.obj K) ⟶ tensorRight K ⋙ Q :=
    a ≫ Functor.whiskerLeft q (tensorRightCounit (q.obj K)) ≫ c
  have := commShift_tensorRightCounit (q.obj K) hK
  have : NatTrans.CommShift a ℤ := by dsimp [a, e, q]; infer_instance
  have : NatTrans.CommShift c ℤ := by dsimp [c, f, e, q]; infer_instance
  have : NatTrans.CommShift τ ℤ := by dsimp [τ]; infer_instance
  have heq (L : CochainComplex A ℤ) : τ.app L = Functor.LaxMonoidal.μ Q L K := by
    dsimp [τ, a, c, f, e, q, tensorRightCounit]
    simp only [Category.id_comp, Category.comp_id]
    change ((_ ▷ _ ≫ _ ◁ _) ≫ Functor.LaxMonoidal.μ (Qh (C := A)) _ _ ≫
      Qh.map (𝟙 _) ≫ _) = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    change (_ ▷ _ ≫ _ ◁ _) ≫ Functor.LaxMonoidal.μ (Qh (C := A)) _ _ ≫ _ =
      (_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ (Qh (C := A)) _ _ ≫ Qh.map (𝟙 _)) ≫ _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, tensorHom_def, Category.assoc]
    erw [Category.id_comp]
  have h := NatTrans.shift_app_comm τ t M
  simp only [Functor.commShiftIso_comp_hom_app, heq, Category.assoc] at h
  convert h.symm using 1 <;> rfl

private lemma tensor_inv_shift (M : CochainComplex A ℤ) (b : B) (t : ℤ) :
    Q.map (mappingCone.shiftIso (b • 𝟙 M) t).inv ≫
        (Q.commShiftIso t).hom.app (mappingCone (b • 𝟙 M)) ≫
        (tensorScalarConeIso M b).inv⟦t⟧' =
      (tensorScalarConeIso (M⟦t⟧) b).inv ≫
        (tensorRight (Q.obj (scalarCone b))).map ((Q.commShiftIso t).hom.app M) ≫
        ((tensorRight (Q.obj (scalarCone b))).commShiftIso t).hom.app (Q.obj M) := by
  have hc := congrArg Q.map (chain_inv_shift M b t)
  have hm := mu_shift M (scalarCone b) t (kFlat_scalarCone b)
  simp only [tensorScalarConeIso, Iso.trans_inv, Functor.mapIso_inv, asIso_inv,
    Functor.map_comp, Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc, hc,
    Functor.map_comp, Category.assoc]
  apply (cancel_mono ((Functor.LaxMonoidal.μ Q M (scalarCone b))⟦t⟧')).mp
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
  rw [← hm]
  simp only [IsIso.inv_hom_id_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The canonical reduction comparison commutes with signed integer shifts.
Source: blueprint derived Nakayama resolution, On X, and first reduction, Cones.
(auxiliary; not a blueprint node).

Proof: the total-tensor comparison on coefficient degrees zero and minus one has
respectively the unitor and the signed unitor as components. Shifting the first
input changes the latter sign by (-1)^t, precisely the inverse cone shift.
Localize this square using the K-flat scalar cone and the shift compatibility
of the derived tensor counit. Naturality of the tensor shift with the localized
augmentation transports the square to the coefficient quotient. -/
theorem reductionIso_inv_signed_shift {b : B} {N : A} {p : 𝟙_ A ⟶ N}
    (w : (b • 𝟙 (𝟙_ A)) ≫ p = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) (M : CochainComplex A ℤ) (t : ℤ) :
    Q.map (CochainComplex.mappingCone.shiftIso (b • 𝟙 M) t).inv ≫
        (Q.commShiftIso t).hom.app (CochainComplex.mappingCone (b • 𝟙 M)) ≫
        (reductionIso w hS M).inv⟦t⟧' =
      (reductionIso w hS (M⟦t⟧)).inv ≫
        (tensorRight ((singleFunctor A 0).obj N)).map
          ((Q.commShiftIso t).hom.app M) ≫
        ((tensorRight ((singleFunctor A 0).obj N)).commShiftIso t).hom.app
          (Q.obj M) := by
  have := isIso_Q_map_scalarConeDesc w hS
  let a := Q.map (scalarConeDesc w)
  let τ : tensorRight (Q.obj (scalarCone b)) ⟶
      tensorRight ((singleFunctor A 0).obj N) := (curriedTensor _).flip.map a
  have hs := NatTrans.shift_app_comm τ t (Q.obj M)
  simp only [reductionIso, Iso.trans_inv, whiskerLeftIso_inv, Iso.symm_inv,
    asIso_hom, Functor.map_comp, Category.assoc]
  have ht := tensor_inv_shift M b t
  rw [← Category.assoc] at ht
  erw [← Category.assoc, ← Category.assoc, ht]
  simp only [Category.assoc]
  dsimp only [τ, a, Functor.flip_map_app, curriedTensor_map_app] at hs
  erw [hs]
  apply (cancel_epi (tensorScalarConeIso (M⟦t⟧) b).inv).2
  rw [← Category.assoc, ← Category.assoc]
  apply (cancel_mono
    (((tensorRight ((singleFunctor A 0).obj N)).commShiftIso t).hom.app (Q.obj M))).2
  exact (whisker_exchange ((Q.commShiftIso t).hom.app M) a).symm

end DerivedCategory
