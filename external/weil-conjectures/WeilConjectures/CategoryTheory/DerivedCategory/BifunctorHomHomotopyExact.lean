/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
import WeilConjectures.Algebra.Homology.BifunctorHomCone

/-!
# Exactness of the signed bifunctor Hom complex on the homotopy category

Source: Stacks Project, Tag 08JC, `lemma-RHom-triangulated`, termwise-split Hom argument,
generalized to a separately additive bifunctor; the signed model is
`CochainComplex.bifunctorHomObj` in
`WeilConjectures.Algebra.Homology.BifunctorHomComplex`.
(auxiliary; not a blueprint node)

The existing `bifunctorHomHomotopyFunctor H I` takes values in the opposite derived
category. Its `leftOp` is the functor from the opposite homotopy category to the derived
category in the node. The source uses the usual opposite triangulation: its shift by
`m` is the underlying shift by `-m`. The shift structure is existential data, and the
triangulated assertion uses that same structure.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

universe u₁ u₂ u₃ v₁ v₂ v₃ w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite

namespace CochainComplex

open Opposite CategoryTheory.Category CategoryTheory.Pretriangulated

private theorem oppositeShiftAdd_inv {D : Type*} [Category D] [HasShift D ℤ]
    (X : D) (r s : ℤ) :
    ((shiftFunctorAdd Dᵒᵖ r s).inv.app (op X)).unop =
      (CategoryTheory.shiftFunctorAdd' D (-r) (-s) (-(r + s)) (by omega)).hom.app X := by
  rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
  rw [shiftFunctorAdd'_op_inv_app _ r s (r + s) rfl (-r) (-s) (-(r + s))
    (by omega) (by omega) (by omega)]
  simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
    unop_comp, Quiver.Hom.unop_op, unop_id]
  erw [unop_id, Category.id_comp]

private theorem oppositeShift_map_unop {D : Type*} [Category D] [HasShift D ℤ]
    {X Y : D} (f : X ⟶ Y) (s : ℤ) :
    ((CategoryTheory.shiftFunctor Dᵒᵖ s).map f.op).unop = f⟦-s⟧' := by
  rfl

section ShiftConstruction

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C] [HasCountableProducts C]
  (H : Aᵒᵖ ⥤ B ⥤ C) [H.Additive] [∀ X : Aᵒᵖ, (H.obj X).Additive]
  (I : CochainComplex B ℤ)

private abbrev shiftSign (r p : ℤ) : ℤˣ := (r * p + r * (r + 1) / 2).negOnePow

private noncomputable def shiftInv (K : CochainComplex A ℤ) (r : ℤ) :
    (bifunctorHomObj H K I)⟦-r⟧ ⟶ bifunctorHomObj H (K⟦r⟧) I where
  f n := bifunctorHomLift H (K⟦r⟧) I n fun p q hpq ↦
    shiftSign r p • bifunctorHomπ H K I (n + -r) (p + r) q (by omega)
  comm' n m hnm := by
    simp only [ComplexShape.up_Rel] at hnm
    subst m
    apply bifunctorHomObj_hom_ext
    intro p q hpq
    simp only [Category.assoc, bifunctorHomLift_π_assoc,
      shiftFunctor_obj_d']
    rw [bifunctorHomObj_d_π H (K⟦r⟧) I n (n + 1) p q hpq (q - 1)
      (p + 1) (by omega) (by omega)]
    simp only [Linear.comp_units_smul, Preadditive.comp_sub, Category.assoc,
      Linear.units_smul_comp]
    erw [bifunctorHomLift_π_assoc, bifunctorHomLift_π_assoc, bifunctorHomLift_π]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp]
    rw [bifunctorHomObj_d_π H K I (n + -r) (n + 1 + -r) (p + r) q
      (by omega) (q - 1) (p + 1 + r) (by omega) (by omega)]
    simp only [shiftFunctor_obj_d', Units.smul_def, op_zsmul, Functor.map_zsmul,
      NatTrans.app_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      smul_sub, smul_smul]
    have h₁ : (-r).negOnePow * (shiftSign r p * (p + r).negOnePow) =
        p.negOnePow * shiftSign r p := by
      simp only [shiftSign, ← Int.negOnePow_add]
      congr 1
      ring
    have h₂ : p.negOnePow * (shiftSign r (p + 1) * r.negOnePow) =
        p.negOnePow * shiftSign r p := by
      simp only [shiftSign, ← Int.negOnePow_add]
      apply (Int.negOnePow_eq_iff _ _).2
      exact ⟨r, by ring⟩
    simp only [← Units.val_mul, h₁, h₂]
    rfl

private noncomputable def shiftHomX (K : CochainComplex A ℤ) (r n : ℤ) :
    (bifunctorHomObj H (K⟦r⟧) I).X n ⟶ ((bifunctorHomObj H K I)⟦-r⟧).X n :=
  bifunctorHomLift H K I (n + -r) fun p q hpq ↦
    shiftSign r (p - r) •
      (bifunctorHomπ H (K⟦r⟧) I n (p - r) q (by omega) ≫
        (H.map (K.XIsoOfEq (show p - r + r = p by omega)).inv.op).app (I.X q))

private theorem projection_reindex (K : CochainComplex A ℤ)
    (n p p' q : ℤ) (hp : p' = p) (hpq : p + n = q) :
    bifunctorHomπ H K I n p' q (by omega) ≫
        (H.map (K.XIsoOfEq hp).inv.op).app (I.X q) =
      bifunctorHomπ H K I n p q hpq := by
  subst p'
  simp

private theorem shiftInv_hom_id (K : CochainComplex A ℤ) (r n : ℤ) :
    (shiftInv H I K r).f n ≫ shiftHomX H I K r n = 𝟙 _ := by
  apply bifunctorHomObj_hom_ext
  intro p q hpq
  dsimp only [shiftHomX, shiftInv]
  rw [Category.assoc, bifunctorHomLift_π, Linear.comp_units_smul, ← Category.assoc]
  erw [bifunctorHomLift_π]
  simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul,
    Category.id_comp]
  exact projection_reindex H I K (n + -r) p (p - r + r) q (by omega) hpq

private theorem shiftHom_inv_id (K : CochainComplex A ℤ) (r n : ℤ) :
    shiftHomX H I K r n ≫ (shiftInv H I K r).f n = 𝟙 _ := by
  apply bifunctorHomObj_hom_ext
  intro p q hpq
  dsimp only [shiftInv]
  rw [Category.assoc, bifunctorHomLift_π, Linear.comp_units_smul]
  dsimp only [shiftHomX]
  erw [bifunctorHomLift_π]
  have e : p + r - r = p := by omega
  simp only [e, Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, op_id, Functor.map_id,
    NatTrans.id_app, Category.comp_id, Category.id_comp]
  exact projection_reindex H I (K⟦r⟧) n p (p + r - r) q e hpq

private noncomputable def shiftIso (K : CochainComplex A ℤ) (r : ℤ) :
    (bifunctorHomObj H K I)⟦-r⟧ ≅ bifunctorHomObj H (K⟦r⟧) I := by
  have (n : ℤ) : IsIso ((shiftInv H I K r).f n) :=
    ⟨⟨shiftHomX H I K r n, shiftInv_hom_id H I K r n,
      shiftHom_inv_id H I K r n⟩⟩
  have : IsIso (shiftInv H I K r) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (shiftInv H I K r)

private noncomputable def ordinaryFunctor :
    CochainComplex A ℤ ⥤ (CochainComplex C ℤ)ᵒᵖ where
  obj K := op (bifunctorHomObj H K I)
  map f := (bifunctorHomMapLeft (H := H) (Y := I) f).op
  map_id K := by rw [bifunctorHomMapLeft_id, op_id]
  map_comp f g := by rw [bifunctorHomMapLeft_comp, op_comp]

private noncomputable def ordinaryShiftIso (r : ℤ) :
    CategoryTheory.shiftFunctor _ r ⋙ ordinaryFunctor H I ≅
      ordinaryFunctor H I ⋙ CategoryTheory.shiftFunctor _ r :=
  NatIso.ofComponents (fun K ↦ (shiftIso H I K r).op) (by
    intro K L f
    apply Quiver.Hom.unop_inj
    apply HomologicalComplex.hom_ext
    intro n
    apply bifunctorHomObj_hom_ext
    intro p q hpq
    change (shiftInv H I L r ≫
      bifunctorHomMapLeft (H := H) (Y := I) (f⟦r⟧')).f n ≫
        bifunctorHomπ H (K⟦r⟧) I n p q hpq =
      ((bifunctorHomMapLeft (H := H) (Y := I) f)⟦-r⟧' ≫ shiftInv H I K r).f n ≫
        bifunctorHomπ H (K⟦r⟧) I n p q hpq
    dsimp only [HomologicalComplex.comp_f, shiftInv]
    simp only [Category.assoc, bifunctorHomLift_π, bifunctorHomMapLeft_f_π,
      bifunctorHomLift_π_assoc, bifunctorHomMapLeft_f_π_assoc,
      shiftFunctor_map_f', Linear.comp_units_smul, Linear.units_smul_comp])

private theorem projection_transport (K : CochainComplex A ℤ)
    (n n' p p' q : ℤ) (hn : n = n') (hp : p = p') (hpq : p + n = q) :
    ((bifunctorHomObj H K I).XIsoOfEq hn).hom ≫
        bifunctorHomπ H K I n' p' q (by omega) ≫
          (H.map (K.XIsoOfEq hp).hom.op).app (I.X q) =
      bifunctorHomπ H K I n p q hpq := by
  subst n' p'
  simp

private theorem ordinaryShiftIso_zero :
    ordinaryShiftIso H I 0 = Functor.CommShift.isoZero (ordinaryFunctor H I) ℤ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rw [Functor.CommShift.isoZero_hom_app]
  apply Quiver.Hom.unop_inj
  rw [shiftFunctorZero_op_inv_app]
  simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.comp_id, Category.id_comp, unop_comp,
    Quiver.Hom.unop_op, unop_id]
  erw [unop_id, Category.id_comp]
  change shiftInv H I K 0 =
    (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app (bifunctorHomObj H K I) ≫
      bifunctorHomMapLeft (H := H) (Y := I)
        ((shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.app K)
  apply HomologicalComplex.hom_ext
  intro n
  apply bifunctorHomObj_hom_ext
  intro p q hpq
  dsimp only [HomologicalComplex.comp_f, shiftInv]
  simp only [Category.assoc, bifunctorHomLift_π, bifunctorHomMapLeft_f_π,
    shiftFunctorZero_hom_app_f, shiftSign, zero_mul, zero_add, Int.zero_ediv,
    Int.negOnePow_zero, one_smul]
  exact (projection_transport H I K (n + 0) n (p + 0) p q
    (by omega) (by omega) (by omega)).symm

private theorem quadratic_add (r s : ℤ) :
    (r + s) * (r + s + 1) / 2 =
      r * (r + 1) / 2 + s * (s + 1) / 2 + r * s := by
  have he (n : ℤ) : 2 ∣ n * (n + 1) := Int.two_dvd_mul_add_one n
  have hr := Int.ediv_mul_cancel (he r)
  have hs := Int.ediv_mul_cancel (he s)
  have hrs := Int.ediv_mul_cancel (he (r + s))
  have h : (r + s) * (r + s + 1) = r * (r + 1) + s * (s + 1) + 2 * (r * s) := by
    ring
  omega

private theorem shiftSign_add (r s p : ℤ) :
    shiftSign (r + s) p = shiftSign s p * shiftSign r (p + s) := by
  simp only [shiftSign, ← Int.negOnePow_add, quadratic_add]
  congr 1
  ring

private theorem ordinaryShiftIso_add (r s : ℤ) :
    ordinaryShiftIso H I (r + s) =
      Functor.CommShift.isoAdd (ordinaryShiftIso H I r) (ordinaryShiftIso H I s) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  rw [Functor.CommShift.isoAdd_hom_app]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, ordinaryFunctor]
  rw [oppositeShiftAdd_inv]
  simp only [Category.assoc, ordinaryShiftIso, NatIso.ofComponents, Iso.op_hom,
    shiftIso, asIso_hom, oppositeShift_map_unop, Quiver.Hom.unop_op]
  change shiftInv H I K (r + s) =
    (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ)
      (-r) (-s) (-(r + s)) (by omega)).hom.app (bifunctorHomObj H K I) ≫
      (shiftInv H I K r)⟦-s⟧' ≫ shiftInv H I (K⟦r⟧) s ≫
        bifunctorHomMapLeft (H := H) (Y := I)
          ((shiftFunctorAdd (CochainComplex A ℤ) r s).hom.app K)
  apply HomologicalComplex.hom_ext
  intro n
  apply bifunctorHomObj_hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Category.assoc, bifunctorHomMapLeft_f_π,
    shiftFunctorAdd'_hom_app_f', shiftFunctorAdd_hom_app_f, shiftFunctor_map_f']
  dsimp only [shiftInv]
  erw [bifunctorHomLift_π, bifunctorHomLift_π_assoc]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
  erw [bifunctorHomLift_π_assoc]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul,
    ← shiftSign_add]
  exact congrArg (fun f ↦ shiftSign (r + s) p • f)
    (projection_transport H I K (n + -(r + s)) (n + -s + -r)
      (p + (r + s)) (p + s + r) q (by omega) (by omega) (by omega)).symm

private noncomputable instance ordinaryCommShift : (ordinaryFunctor H I).CommShift ℤ where
  commShiftIso := ordinaryShiftIso H I
  commShiftIso_zero := ordinaryShiftIso_zero H I
  commShiftIso_add := ordinaryShiftIso_add H I

variable [HasDerivedCategory.{w} C]

private noncomputable instance complexCommShift :
    (bifunctorHomComplexFunctor H I).CommShift ℤ :=
  inferInstanceAs ((ordinaryFunctor H I ⋙
    (HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).op).CommShift ℤ)

private noncomputable instance liftedCommShift :
    (bifunctorHomHomotopyFunctor H I).CommShift ℤ := by
  change (CategoryTheory.Quotient.lift _ (bifunctorHomComplexFunctor H I) _).CommShift ℤ
  exact CategoryTheory.Quotient.liftCommShift _ _ _ _

private noncomputable instance leftOpCommShift :
    (bifunctorHomHomotopyFunctor H I).leftOp.CommShift ℤ :=
  inferInstanceAs (((bifunctorHomHomotopyFunctor H I).op ⋙
    CategoryTheory.unopUnop (DerivedCategory C)).CommShift ℤ)

private noncomputable abbrev oppositeCoconeTriangle {X Y : CochainComplex C ℤ} (t : X ⟶ Y) :=
  (triangleOpEquivalence (CochainComplex C ℤ)).functor.obj
    (op (mappingCocone.triangle t))

omit [HasCountableProducts C] [HasDerivedCategory C] in
private theorem oppositeCoconeBoundary_f {X Y : CochainComplex C ℤ}
    (t : X ⟶ Y) (n : ℤ) :
    ((oppositeCoconeTriangle t).mor₃.unop).f n = (mappingCone.inr t).f (n + -1) := by
  dsimp only [oppositeCoconeTriangle, triangleOpEquivalence,
    TriangleOpEquivalence.functor, Triangle.mk]
  simp only [unop_comp, shiftFunctor_op_map _ 1 (-1) (by omega), shiftFunctorOpIso,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.comp_id,
    Category.id_comp, Quiver.Hom.unop_op]
  dsimp only [opShiftFunctorEquivalence, shiftFunctorOpIso]
  simp only [unop_comp, Quiver.Hom.unop_op, Category.comp_id, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.comp_id,
    Iso.trans_hom, Iso.symm_hom, NatIso.op_inv, Iso.symm_inv, NatTrans.op_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    HomologicalComplex.comp_f, shiftFunctor_map_f', mappingCocone.triangle,
    mappingCone.triangle, Triangle.mk, shiftFunctorCompIsoId,
    shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]
  erw [unop_id, HomologicalComplex.id_f, Category.id_comp,
    unop_id, HomologicalComplex.id_f]
  simp only [Category.assoc, Category.id_comp, mappingCocone, XIsoOfEq_shift,
    HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
    Functor.opId, Iso.refl_inv, NatTrans.id_app, unop_id, HomologicalComplex.id_f]
  erw [unop_id, HomologicalComplex.id_f, Category.comp_id, Category.id_comp,
    HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

private theorem coneTriangle_boundary_f {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) :
    (mappingCone.triangle f).mor₃.f p =
      -(mappingCone.fst f).1.v p (p + 1) rfl := by
  dsimp only [mappingCone.triangle, Triangle.mk, HomComplex.Cocycle.homOf_f,
    HomComplex.Cocycle.rightShift_coe]
  rw [HomComplex.Cochain.rightShift_v _ 1 0 (zero_add 1)
    p p (add_zero p) (p + 1) rfl]
  simp [shiftFunctorObjXIso]

omit [HasCountableProducts C] [HasDerivedCategory C] in
private theorem coneTarget_ext {X Y : CochainComplex C ℤ} (t : X ⟶ Y)
    {Z : C} (n : ℤ) {a b : Z ⟶ (mappingCone t).X (n - 1)}
    (hx : a ≫ (mappingCone.fst t).1.v (n - 1) n (by omega) =
      b ≫ (mappingCone.fst t).1.v (n - 1) n (by omega))
    (hy : a ≫ (mappingCone.snd t).v (n - 1) (n - 1) (by omega) =
      b ≫ (mappingCone.snd t).v (n - 1) (n - 1) (by omega)) : a = b := by
  exact (mappingCone.ext_to_iff t (n - 1) n (by omega) a b).2 ⟨hx, hy⟩

omit [HasDerivedCategory C] in
private theorem cone_boundary {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (θ : bifunctorHomObj H (mappingCone f) I ≅
      (mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧)
    (hy : ∀ (n p q : ℤ) (hpq : p + n = q),
      θ.hom.f n ≫ bifunctorHomConeY H I f n ≫
          bifunctorHomπ H K I (n - 1) (p + 1) q (by omega) =
        p.negOnePow • (bifunctorHomπ H (mappingCone f) I n p q hpq ≫
          (H.map ((mappingCone.inl f).v (p + 1) p (by omega)).op).app (I.X q)))
    (hx : ∀ (n p q : ℤ) (hpq : p + n = q),
      θ.hom.f n ≫ bifunctorHomConeX H I f n ≫
          bifunctorHomπ H L I n p q hpq =
        bifunctorHomπ H (mappingCone f) I n p q hpq ≫
          (H.map ((mappingCone.inr f).f p).op).app (I.X q)) :
    shiftInv H I K 1 ≫ bifunctorHomMapLeft (H := H) (Y := I)
        (mappingCone.triangle f).mor₃ ≫ θ.hom =
      (oppositeCoconeTriangle (bifunctorHomMapLeft (H := H) (Y := I) f)).mor₃.unop := by
  apply HomologicalComplex.hom_ext
  intro n
  let t := bifunctorHomMapLeft (H := H) (Y := I) f
  rw [oppositeCoconeBoundary_f]
  have hxy := hx
  have hyy := hy
  dsimp only [bifunctorHomConeX, bifunctorHomConeY, shiftFunctorObjXIso] at hxy hyy
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp] at hxy hyy
  dsimp only [shiftFunctor_obj_X', shiftFunctor_obj_X] at hxy hyy
  simp only [Category.id_comp, Category.assoc] at hxy hyy
  apply coneTarget_ext t n
  · apply bifunctorHomObj_hom_ext
    intro p q hpq
    dsimp only [HomologicalComplex.comp_f]
    simp only [Category.assoc]
    erw [hxy n p q hpq]
    erw [bifunctorHomMapLeft_f_π_assoc]
    dsimp only [shiftInv]
    erw [bifunctorHomLift_π_assoc]
    dsimp only [t]
    simp only [Linear.units_smul_comp, coneTriangle_boundary_f, op_neg,
      Functor.map_neg, NatTrans.app_neg, Preadditive.comp_neg, Preadditive.neg_comp,
      Category.assoc]
    erw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, mappingCone.inr_f_fst_v]
    simp only [op_zero, Functor.map_zero, NatTrans.app_zero, comp_zero, smul_zero,
      neg_zero, mappingCone.inr_f_fst_v_assoc, zero_comp]
    erw [mappingCone.inr_f_fst_v_assoc, zero_comp]
  · apply bifunctorHomObj_hom_ext
    intro p q hpq
    obtain ⟨p, rfl⟩ : ∃ a : ℤ, p = a + 1 := ⟨p - 1, by omega⟩
    dsimp only [HomologicalComplex.comp_f]
    simp only [Category.assoc]
    erw [hyy n p q (by omega)]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp]
    erw [bifunctorHomMapLeft_f_π_assoc]
    dsimp only [shiftInv]
    erw [bifunctorHomLift_π_assoc]
    dsimp only [t]
    simp only [Linear.units_smul_comp, smul_smul, coneTriangle_boundary_f,
      op_neg, Functor.map_neg, NatTrans.app_neg, Preadditive.comp_neg,
      ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
      mappingCone.inl_v_fst_v, op_id, Functor.map_id, NatTrans.id_app,
      Category.comp_id, mappingCone.inr_f_snd_v_assoc, Category.id_comp]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
    erw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
      mappingCone.inl_v_fst_v]
    simp only [op_id, Functor.map_id, NatTrans.id_app, Category.comp_id,
      smul_neg]
    have hs : p.negOnePow * shiftSign 1 p = -1 := by
      simp only [shiftSign, one_mul, Int.reduceAdd, Int.reduceDiv, ← Int.negOnePow_add]
      rw [show p + (p + 1) = 2 * p + 1 by omega, Int.negOnePow_add,
        Int.negOnePow_two_mul, Int.negOnePow_one]
      simp
    rw [hs]
    simp only [Units.neg_smul, one_smul, neg_neg]
    erw [mappingCone.inr_f_snd_v_assoc, CategoryTheory.Functor.map_id]
    simp only [NatTrans.id_app, Category.comp_id]
    rfl

omit [HasDerivedCategory C] in
private theorem ordinaryConeTriangle {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    Nonempty (oppositeCoconeTriangle (bifunctorHomMapLeft (H := H) (Y := I) f) ≅
      (ordinaryFunctor H I).mapTriangle.obj (mappingCone.triangle f)) := by
  obtain ⟨θ, hθ, _⟩ := exists_signedBifunctorConeIso H I
  obtain ⟨hy, hx, _, _, hi, _, _⟩ := hθ K L f
  refine ⟨Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (θ K L f).op ?_ ?_ ?_⟩
  · simp [oppositeCoconeTriangle, ordinaryFunctor]
  · apply Quiver.Hom.unop_inj
    change (θ K L f).hom ≫ mappingCocone.fst
        (bifunctorHomMapLeft (H := H) (Y := I) f) =
      bifunctorHomMapLeft (H := H) (Y := I) (mappingCone.inr f) ≫ 𝟙 _
    rw [Category.comp_id]
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, hi]
    congr 1
    simp only [mappingCocone.fst, HomologicalComplex.neg_f_apply,
      HomComplex.Cocycle.homOf_f, HomComplex.Cocycle.leftShift_coe,
      HomComplex.Cochain.leftShift_v _ (-1) 0 (add_neg_cancel 1)
        n n (add_zero n) (n - 1) (by omega),
      HomComplex.Cochain.units_smul_v, Int.negOnePow_one, Units.neg_smul,
      one_smul, neg_neg, bifunctorHomConeX, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    norm_num
  · apply Quiver.Hom.unop_inj
    simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    dsimp only [Functor.mapTriangle, ordinaryFunctor, ordinaryCommShift,
      Functor.commShiftIso, ordinaryShiftIso, NatIso.ofComponents, Iso.op_hom,
      shiftIso, asIso_hom, unop_comp, Quiver.Hom.unop_op, Triangle.mk_mor₃,
      mappingCone.triangle, Triangle.mk_obj₁]
    rw [Category.assoc]
    change (oppositeCoconeTriangle (bifunctorHomMapLeft (H := H) (Y := I) f)).mor₃.unop =
      shiftInv H I K 1 ≫ bifunctorHomMapLeft (H := H) (Y := I)
        (mappingCone.triangle f).mor₃ ≫ (θ K L f).hom
    exact (cone_boundary H I f (θ K L f) hy hx).symm

private noncomputable def quotientComparison :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ bifunctorHomHomotopyFunctor H I ≅
      bifunctorHomComplexFunctor H I := by
  change CategoryTheory.Quotient.functor _ ⋙ CategoryTheory.Quotient.lift _ _ _ ≅ _
  exact CategoryTheory.Quotient.lift.isLift _ _ _

private instance quotientComparison_commShift :
    NatTrans.CommShift (quotientComparison H I).hom ℤ := by
  change NatTrans.CommShift (CategoryTheory.Quotient.lift.isLift _ _ _).hom ℤ
  exact CategoryTheory.Quotient.liftCommShift_compatibility _ _ _ _

private theorem homotopyCone_distinguished {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (bifunctorHomHomotopyFunctor H I).mapTriangle.obj (mappingCone.triangleh f) ∈
      distTriang (DerivedCategory C)ᵒᵖ := by
  obtain ⟨e⟩ := ordinaryConeTriangle H I f
  let t := bifunctorHomMapLeft (H := H) (Y := I) f
  have : NatTrans.CommShift (Functor.isoWhiskerLeft (ordinaryFunctor H I)
      (NatIso.op (DerivedCategory.quotientCompQhIso C))).hom ℤ := by
    dsimp only [Functor.isoWhiskerLeft_hom, NatIso.op_hom]
    infer_instance
  let e' : (bifunctorHomHomotopyFunctor H I).mapTriangle.obj (mappingCone.triangleh f) ≅
      DerivedCategory.Q.op.mapTriangle.obj (oppositeCoconeTriangle t) :=
    (Functor.mapTriangleCompIso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (bifunctorHomHomotopyFunctor H I)).symm.app _ ≪≫
    (Functor.mapTriangleIso (quotientComparison H I)).app _ ≪≫
    (Functor.mapTriangleIso (Functor.isoWhiskerLeft (ordinaryFunctor H I)
      (NatIso.op (DerivedCategory.quotientCompQhIso C)))).symm.app _ ≪≫
    (Functor.mapTriangleCompIso (ordinaryFunctor H I) DerivedCategory.Q.op).app _ ≪≫
    DerivedCategory.Q.op.mapTriangle.mapIso e.symm
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (op_distinguished _ (DerivedCategory.mappingCocone_triangle_distinguished t)) _
    (e' ≪≫ (DerivedCategory.Q.mapTriangleOpCompTriangleOpEquivalenceFunctorApp
      (mappingCocone.triangle t)).symm)

private theorem homotopyExact : (bifunctorHomHomotopyFunctor H I).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨K, L, f, ⟨e⟩⟩ := hT
    exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
      (homotopyCone_distinguished H I f) _
      ((bifunctorHomHomotopyFunctor H I).mapTriangle.mapIso e)

end ShiftConstruction

/-- The signed Hom functor of an arbitrary separately additive bifunctor admits coherent
commutation with all integer shifts making it triangulated on the opposite homotopy category.
No K-injectivity of `I`, exactness of products, or preservation of quasi-isomorphisms is needed.

Source: Stacks Project, Tag 08JC, `lemma-RHom-triangulated`; the arbitrary-bifunctor signed
calculation is the explicit generalization in the blueprint proof.
(auxiliary; not a blueprint node)

Proof plan, following the five steps of the node:
1. Put `U(K) = bifunctorHomObj H K I`. Its degree `n` is the product over `p + n = q`.
   On the `(p,q)` projection its differential is `(-1)^p` times postcomposition by `d_I`
   minus precomposition by `d_K`. The pure terms of its square vanish by `d^2 = 0`;
   the mixed terms cancel by naturality and the opposite signs for consecutive `p`.
   Precomposition defines an additive contravariant functor on complexes.
2. If `f - g = d h + h d`, precomposition by `h^p` with multiplier `(-1)^p` is a
   degree-minus-one homotopy between `U(f)` and `U(g)`: the `d_I` terms cancel and the
   remaining terms give precomposition by `f - g`. Thus the existing quotient lift
   `bifunctorHomHomotopyFunctor` is defined on homotopy classes, before any localization.
3. For an integer `r`, set `b(r) = r(r+1)/2`. Reindex by `j = p+r` and multiply the
   original `p` factor by `(-1)^(r*p+b(r))` to obtain `U(K[r]) ≅ U(K)[-r]`.
   The signs at consecutive `p` differ by `(-1)^r`, so this is a chain isomorphism,
   natural in `K`. The identity `b(r+s)=b(r)+b(s)+r*s` gives the addition coherence;
   at zero the comparison is the identity. On the opposite source use `r = -m`.
4. For `f : K ⟶ L`, use `lem-sf-signed-bifunctor-cone-iso` to identify
   `U(Cone(f))` with `Cone(U(f))[-1]`. In coordinates `(y,x)` the differential is
   `(-d y - U(f) x, d x)`, and `U(i)` is projection to `x`. For the third arrow of
   the reversed cone triangle, `w[-1]` with `w = -projection`, the shift comparison
   contributes `(-1)^(j+1)` and the minus projection contributes another minus.
   The cone comparison contributes `(-1)^j`, giving the inclusion of `y` into
   `Cone(U(f))`. This is exactly the inverse rotation of the cone triangle of `U(f)`.
   By `lem-pur-homotopy-category-triangulated`, cone triangles and their inverse
   rotations are distinguished and every distinguished triangle is isomorphic to one.
5. Compose with the exact localization `DerivedCategory.Qh` from
   `lem-pur-homotopy-category-triangulated`. Its coherent shift structure preserves
   the zero and addition laws, and it preserves the distinguished triangles of step 4.
   The resulting functor is precisely `(bifunctorHomHomotopyFunctor H I).leftOp`.
-/
theorem bifunctorHomHomotopyFunctor_leftOp_exact
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Abelian A] [Abelian B] [Abelian C] [HasCountableProducts C]
    [HasDerivedCategory.{w} C] (H : Aᵒᵖ ⥤ B ⥤ C)
    [H.Additive] [∀ X : Aᵒᵖ, (H.obj X).Additive] (I : CochainComplex B ℤ) :
    ∃ (_ : (bifunctorHomHomotopyFunctor H I).leftOp.CommShift ℤ),
      (bifunctorHomHomotopyFunctor H I).leftOp.IsTriangulated := by
  let := homotopyExact H I
  refine ⟨leftOpCommShift H I, ?_⟩
  exact inferInstanceAs (((bifunctorHomHomotopyFunctor H I).op ⋙
    CategoryTheory.unopUnop (DerivedCategory C)).IsTriangulated)

end CochainComplex
