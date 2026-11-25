/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechConstruction
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechSectionCoordinates

/-! # Localization coordinates of the ordered Čech fibre

Source: Stacks Project, Tag 099D(d), Cohomology, ordered Čech complexes.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
namespace AlgebraicGeometry

noncomputable section

private def coneFstIso {D : Type*} [Category D] [Preadditive D]
    [HasBinaryBiproducts D] {K L : CochainComplex D ℤ} (g : K ⟶ L)
    (i j : ℤ) (hij : i + 1 = j) (hz : IsZero (L.X i)) :
    (CochainComplex.mappingCone g).X i ≅ K.X j where
  hom := (CochainComplex.mappingCone.fst g).1.v i j hij
  inv := (CochainComplex.mappingCone.inl g).v j i (by omega)
  hom_inv_id := by
    have h := CochainComplex.mappingCone.id_X g i j hij
    have hzero : (CochainComplex.mappingCone.snd g).v i i (add_zero i) = 0 :=
      hz.eq_of_tgt _ _
    simpa only [hzero, zero_comp, add_zero] using h
  inv_hom_id := CochainComplex.mappingCone.inl_v_fst_v g j i hij

private def coneSndIso {D : Type*} [Category D] [Preadditive D]
    [HasBinaryBiproducts D] {K L : CochainComplex D ℤ} (g : K ⟶ L)
    (i j : ℤ) (hij : i + 1 = j) (hz : IsZero (K.X j)) :
    (CochainComplex.mappingCone g).X i ≅ L.X i where
  hom := (CochainComplex.mappingCone.snd g).v i i (add_zero i)
  inv := (CochainComplex.mappingCone.inr g).f i
  hom_inv_id := by
    have h := CochainComplex.mappingCone.id_X g i j hij
    have hzero : (CochainComplex.mappingCone.fst g).1.v i j hij = 0 :=
      hz.eq_of_tgt _ _
    simpa only [hzero, zero_comp, zero_add] using h
  inv_hom_id := CochainComplex.mappingCone.inr_f_snd_v g i

private theorem sectionsNegative (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (n : ℤ) (hn : n < 0) :
    IsZero ((ringComplexOrderedCechSections A I f).X n) := by
  apply (ringComplexSectionScalars A I).map_isZero
  apply HomologicalComplex.isZero_extend_X
  intro k hk
  change (k : ℤ) = n at hk
  omega

private def fibreZeroIso (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) :
    (ringComplexOrderedCech A I f).X 0 ≅ ringComplexUnit A :=
  CochainComplex.shiftFunctorObjXIso _ (-1) 0 (-1) rfl ≪≫
    coneFstIso (ringComplexOrderedCechRestriction A I f) (-1) 0 (by omega)
      (sectionsNegative A I f (-1) (by omega)) ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)

private def fibrePositiveIso (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (q : ℕ) :
    (ringComplexOrderedCech A I f).X ((q : ℤ) + 1) ≅
      (ringComplexOrderedCechSections A I f).X (q : ℤ) :=
  CochainComplex.shiftFunctorObjXIso _ (-1) ((q : ℤ) + 1) (q : ℤ) (by omega) ≪≫
    coneSndIso (ringComplexOrderedCechRestriction A I f) (q : ℤ) ((q : ℤ) + 1) rfl
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A)
        ((q : ℤ) + 1) (by omega))

private theorem fibreNegative (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (n : ℤ) (hn : n < 0) :
    IsZero ((ringComplexOrderedCech A I f).X n) := by
  change IsZero ((CochainComplex.mappingCone
    (ringComplexOrderedCechRestriction A I f)).X (n + -1))
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A)
      (n + -1 + 1) (by omega)
  · exact sectionsNegative A I f _ (by omega)

private theorem shiftNegative_d {D : Type*} [Category D] [Preadditive D]
    (K : CochainComplex D ℤ) (i j m n : ℤ)
    (hm : m = i + -1) (hn : n = j + -1) :
    (K⟦(-1 : ℤ)⟧).d i j ≫ (K.shiftFunctorObjXIso (-1) j n hn).hom =
      -(K.shiftFunctorObjXIso (-1) i m hm).hom ≫ K.d m n := by
  simp only [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, Preadditive.neg_comp, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.d_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_hom_comp_d]

private theorem fibreFirst_d (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) :
    (ringComplexOrderedCech A I f).d 0 1 ≫ (fibrePositiveIso A I f 0).hom =
      -(fibreZeroIso A I f).hom ≫ ringComplexOrderedCechFirst A I f := by
  let g := ringComplexOrderedCechRestriction A I f
  have hzero : (CochainComplex.mappingCone.snd g).v (-1) (-1) (add_zero _) = 0 :=
    (sectionsNegative A I f (-1) (by omega)).eq_of_tgt _ _
  change ((CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧).d 0 1 ≫
      ((CochainComplex.mappingCone g).shiftFunctorObjXIso (-1) 1 0 rfl).hom ≫
      (CochainComplex.mappingCone.snd g).v 0 0 (add_zero _) =
    -(((CochainComplex.mappingCone g).shiftFunctorObjXIso (-1) 0 (-1) rfl).hom ≫
      (CochainComplex.mappingCone.fst g).1.v (-1) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom) ≫
        ringComplexOrderedCechFirst A I f
  rw [← Category.assoc, shiftNegative_d (CochainComplex.mappingCone g) 0 1 (-1) 0 rfl rfl]
  simp only [Preadditive.neg_comp, Category.assoc,
    CochainComplex.mappingCone.d_snd_v g (-1) 0 (by omega), hzero, zero_comp,
    add_zero]
  dsimp only [g, ringComplexOrderedCechRestriction]
  rw [HomologicalComplex.mkHomFromSingle_f]

private theorem fibrePositive_d (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (q : ℕ) :
    (ringComplexOrderedCech A I f).d ((q : ℤ) + 1) ((q : ℤ) + 2) ≫
        (fibrePositiveIso A I f (q + 1)).hom =
      -(fibrePositiveIso A I f q).hom ≫
        (ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1) := by
  let g := ringComplexOrderedCechRestriction A I f
  have hzero : (CochainComplex.mappingCone.fst g).1.v
      (q : ℤ) ((q : ℤ) + 1) rfl = 0 :=
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A)
      ((q : ℤ) + 1) (by omega)).eq_of_tgt _ _
  change ((CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧).d
      ((q : ℤ) + 1) ((q : ℤ) + 2) ≫
      ((CochainComplex.mappingCone g).shiftFunctorObjXIso (-1)
        ((q : ℤ) + 2) ((q : ℤ) + 1) (by omega)).hom ≫
      (CochainComplex.mappingCone.snd g).v ((q : ℤ) + 1) ((q : ℤ) + 1) (add_zero _) =
    -(((CochainComplex.mappingCone g).shiftFunctorObjXIso (-1)
        ((q : ℤ) + 1) (q : ℤ) (by omega)).hom ≫
      (CochainComplex.mappingCone.snd g).v (q : ℤ) (q : ℤ) (add_zero _)) ≫
        (ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1)
  rw [← Category.assoc, shiftNegative_d (CochainComplex.mappingCone g) _ _ (q : ℤ) ((q : ℤ) + 1)
    (by omega) (by omega)]
  simp only [Preadditive.neg_comp, Category.assoc,
    CochainComplex.mappingCone.d_snd_v g (q : ℤ) ((q : ℤ) + 1) rfl,
    hzero, zero_comp, zero_add]

private theorem coneAugmentation_zero {D : Type*} [Category D] [Preadditive D]
    [HasBinaryBiproducts D] {K L : CochainComplex D ℤ} (g : K ⟶ L) :
    (CochainComplex.mappingCone.triangle g).invRotate.mor₁.f 0 =
      (CochainComplex.mappingCone.fst g).1.v (-1) 0 (by omega) := by
  simp [CategoryTheory.Pretriangulated.Triangle.invRotate,
    CochainComplex.mappingCone.triangle,
    CochainComplex.HomComplex.Cochain.rightShift_v _ 1 0 (zero_add 1)
      (-1) (-1) (by omega) 0 (by omega),
    shiftFunctorCompIsoId, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorZero_hom_app_f]

private theorem fibreAugmentation (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) :
    (ringComplexOrderedCechAugmentation A I f).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom =
        (fibreZeroIso A I f).hom := by
  rw [ringComplexOrderedCechAugmentation, coneAugmentation_zero]
  rfl

private def signs (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (q : ℕ) : M ≃ₗ[A] M :=
  (LinearEquiv.neg A) ^ (q + 1)

private theorem signs_apply (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (q : ℕ)
    (x : M) : signs A M q x = (-1 : ℤ) ^ (q + 1) • x := by
  have hpow (n : ℕ) : (LinearEquiv.neg A ^ n) x = (-1 : ℤ) ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.neg_apply, ih, pow_succ]
      simp only [mul_neg, mul_one, neg_smul]
  exact hpow (q + 1)

/-- The explicitly constructed ordered Čech fibre has the localization coordinates
and augmentation of the extended ordered complex.
Source: Stacks Project, Tag 099D(d), and Cohomology, Tags 01EQ and 01FJ.
(auxiliary; not a blueprint node)

Proof: every generator belongs to I, so each principal open D(f_i) lies in the
ideal complement. An ordered intersection is D(product f(t i)). The sections of
the structure module there identify, as A-modules, with the corresponding
localization, by the principal-open section isomorphism. Under those isomorphisms
restriction is the unique A-algebra map of localizations; use these maps for l.
The ordered Čech complex was constructed from the products of these sections
and their signed face restrictions. Its inverse-rotated cone adds A in degree
zero and has zero terms in negative degrees. Projection to A is the identity
in degree zero. Identify each positive degree of the cone with the preceding
Čech degree, negating successive coordinates so that the shifted cone
signs become precisely the displayed positive first differential and signed
face sum. These coordinate signs do not change the degree-zero projection.
This proves each equation by substitution in the cone differential. For r=0
the section products are zero modules and the fibre is A[0]; a zero generator
has empty principal open and zero localization, while repeated generators have
the same restriction formulas. The zero ring is included in these formulas. -/
theorem ringComplexOrderedCech_coordinates (A : CommRingCat.{u}) (I : Ideal A)
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) :
    let C := ringComplexOrderedCech A I f
    let a := ringComplexOrderedCechAugmentation A I f
    ∃ (e₀ : (C.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
          (e : ∀ q : ℕ, (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
            ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
          (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
            Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
              Localization.Away (∏ i, f (t i))),
          (∀ n : ℤ, n < 0 → IsZero (C.X n)) ∧
          (∀ (x : (C.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
            e 0 ((C.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
              algebraMap A (Localization.Away (∏ i, f (t i))) (e₀ x)) ∧
          (∀ (q : ℕ) (x : (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
            (t : Fin (q + 2) ↪o Fin r),
            e (q + 1) ((C.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
              (op ⟨PUnit.unit⟩) x) t =
              ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
                l q t j (e q x ((Fin.succAboveOrderEmb j).trans t))) ∧
          (∀ x : (C.X 0).val.obj (op ⟨PUnit.unit⟩),
            (a.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
                (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (CochainComplex.onePointRingSheaf.{u} A)))).hom).val.app
                    (op ⟨PUnit.unit⟩) x = e₀ x) := by
  classical
  dsimp only
  obtain ⟨E, l, hfirst, hd⟩ := ringComplexOrderedCech_sections_coordinates A I r f hf
  let ev : RingSiteModules A ⥤ ModuleCat.{u} A := SheafOfModules.evaluation
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf.{u} A)) (op ⟨PUnit.unit⟩)
  let e₀ := (ev.mapIso (fibreZeroIso A I f)).toLinearEquiv
  let s (q : ℕ) := (ev.mapIso (fibrePositiveIso A I f q)).toLinearEquiv
  let e (q : ℕ) := (s q).trans ((signs A _ q).trans (E q))
  refine ⟨e₀, e, l, fibreNegative A I f, ?_, ?_, ?_⟩
  · intro x t
    have h := congrArg (fun z ↦ z.val.app (op ⟨PUnit.unit⟩) x) (fibreFirst_d A I f)
    change s 0 (((ringComplexOrderedCech A I f).d 0 1).val.app
      (op ⟨PUnit.unit⟩) x) =
        -((ringComplexOrderedCechFirst A I f).val.app (op ⟨PUnit.unit⟩) (e₀ x)) at h
    change E 0 (signs A _ 0 (s 0 _)) t = _
    rw [h]
    simp only [signs, zero_add, pow_one, LinearEquiv.neg_apply, neg_neg]
    exact hfirst (e₀ x) t
  · intro q x t
    have h := congrArg (fun z ↦ z.val.app (op ⟨PUnit.unit⟩) x) (fibrePositive_d A I f q)
    change s (q + 1) (((ringComplexOrderedCech A I f).d
      ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app (op ⟨PUnit.unit⟩) x) =
        -(((ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1)).val.app
          (op ⟨PUnit.unit⟩) (s q x)) at h
    change E (q + 1) (signs A _ (q + 1) (s (q + 1) _)) t = _
    rw [h]
    have hs : signs A _ (q + 1)
        (-(((ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1)).val.app
          (op ⟨PUnit.unit⟩) (s q x))) =
        ((ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1)).val.app
          (op ⟨PUnit.unit⟩) (signs A _ q (s q x)) := by
      change signs A _ (q + 1)
        (-(((ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1)).val.app
          (op ⟨PUnit.unit⟩)).hom (s q x)) =
        (((ringComplexOrderedCechSections A I f).d (q : ℤ) ((q : ℤ) + 1)).val.app
          (op ⟨PUnit.unit⟩)).hom (signs A _ q (s q x))
      simp only [signs_apply, map_neg, map_zsmul, pow_succ, mul_neg, mul_one,
        neg_smul, neg_neg]
    erw [hs]
    exact hd q (signs A _ q (s q x)) t
  · intro x
    exact congrArg (fun z ↦ z.val.app (op ⟨PUnit.unit⟩) x) (fibreAugmentation A I f)

end
end AlgebraicGeometry
