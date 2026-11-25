/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import all WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # The normalized exact structure on contravariant derived internal Hom

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X and 08JC.
(blueprint: lem-coef-signed-derived-internal-hom-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite
attribute [local irreducible] CategoryTheory.homComplexFunctor

namespace CategoryTheory.SignedDoubleHomCone.Calculation
open CochainComplex CochainComplex.HomComplex
variable {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
  {U : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ}

private def coneAlpha {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    Cochain (hc U G I) (hc U (HomologicalComplex.homotopyCofiber f) I) 0 :=
  Cochain.ofHoms (inB P I f)

private def coneBetaCochain {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    Cochain (hc U E I) (hc U (HomologicalComplex.homotopyCofiber f) I) 1 :=
  Cochain.mk (fun q q' h ↦
    (q.negOnePow • inA P I f q) ≫
      ((hc U (HomologicalComplex.homotopyCofiber f) I).XIsoOfEq (show q + 1 = q' by omega)).hom)

private theorem coneBetaCochain_v {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) (q : ℤ) :
    (coneBetaCochain P I f).v q (q + 1) rfl = q.negOnePow • inA P I f q := by
  simp only [coneBetaCochain, Cochain.mk_v, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id]

private def coneBeta {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    Cocycle (hc U E I) (hc U (HomologicalComplex.homotopyCofiber f) I) 1 :=
  Cocycle.mk (coneBetaCochain P I f) 2 rfl (by
    ext q q' h
    have hq : q' = q + 1 + 1 := by omega
    subst hq
    rw [δ_v 1 2 rfl _ q (q + 1 + 1) (by omega) (q + 1) (q + 1) (by omega) rfl]
    simp only [coneBetaCochain_v, Linear.units_smul_comp, Linear.comp_units_smul,
      inA_d, Int.negOnePow_succ, Units.neg_smul, one_smul,
      show Int.negOnePow 2 = 1 from rfl, Preadditive.comp_neg,
      Linear.comp_units_smul, add_neg_cancel, Cochain.zero_v])

/- The defect of the unsigned G-summand inclusion is canceled by the signed E-summand. -/
attribute [local irreducible] coneBeta

private theorem coneAlphaBeta {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    δ 0 1 (coneAlpha P I f) +
      (Cochain.ofHom ((dualF U I).map f.op)).comp (coneBeta P I f).1 (zero_add 1) = 0 := by
  ext q q' h
  have hq : q' = q + 1 := by omega
  subst hq
  rw [Cochain.add_v, Cochain.zero_v, δ_v 0 1 (zero_add 1) _ q (q + 1) rfl q
    (q + 1) (by omega) rfl]
  simp only [coneAlpha, Cochain.ofHoms_v]
  rw [Cochain.comp_v (n₁ := 0) (n₂ := 1) _ _ _ q q (q + 1) (by omega) rfl]
  simp only [coneBeta, Cocycle.mk_coe, coneBetaCochain_v, Cochain.ofHom_v]
  rw [inB_d P I f q]
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul,
    Linear.comp_units_smul, Int.negOnePow_succ]
  abel

private def ordinaryConeComparison {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    mappingCocone ((dualF U I).map f.op) ⟶ hc U (HomologicalComplex.homotopyCofiber f) I :=
  mappingCocone.desc _ (coneAlpha P I f) (coneBeta P I f) (coneAlphaBeta P I f)

attribute [local irreducible] ordinaryConeComparison

private theorem ordinaryConeComparison_inl {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) (q : ℤ) :
    (mappingCocone.inl ((dualF U I).map f.op)).v q q (add_zero q) ≫
      (ordinaryConeComparison P I f).f q = inB P I f q := by
  simpa only [ordinaryConeComparison, coneAlpha, Cochain.ofHoms_v] using
    mappingCocone.inl_v_desc_f ((dualF U I).map f.op)
      (coneAlpha P I f) (coneBeta P I f) (coneAlphaBeta P I f) q

private theorem ordinaryConeComparison_inr {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) (q : ℤ) :
    (mappingCocone.inr ((dualF U I).map f.op)).1.v q (q + 1) rfl ≫
      (ordinaryConeComparison P I f).f (q + 1) = q.negOnePow • inA P I f q := by
  simpa only [ordinaryConeComparison, coneBeta, Cocycle.mk_coe, coneBetaCochain_v] using
    mappingCocone.inr_v_desc_f ((dualF U I).map f.op)
      (coneAlpha P I f) (coneBeta P I f) (coneAlphaBeta P I f) q (q + 1) rfl

/- The inverse restricts to the two cone summands, with the same involutive sign. -/
private theorem ordinaryConeComparison_isIso {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    IsIso (ordinaryConeComparison P I f) := by
  suffices hh : ∀ t, IsIso ((ordinaryConeComparison P I f).f (t + 1)) by
    have hq (q : ℤ) : IsIso ((ordinaryConeComparison P I f).f q) := by
      have he : q - 1 + 1 = q := by omega
      exact he ▸ hh (q - 1)
    letI := hq
    exact HomologicalComplex.Hom.isIso_of_components _
  intro t
  let g : (hc U (HomologicalComplex.homotopyCofiber f) I).X (t + 1) ⟶
      (mappingCocone ((dualF U I).map f.op)).X (t + 1) :=
    outB P I f (t + 1) ≫
      (mappingCocone.inl ((dualF U I).map f.op)).v (t + 1) (t + 1) (by omega) +
      t.negOnePow • (outA P I f (t + 1) t rfl ≫
        (mappingCocone.inr ((dualF U I).map f.op)).1.v t (t + 1) rfl)
  refine ⟨⟨g, ?_, ?_⟩⟩
  · have hext {T : A}
        {a b : (mappingCocone ((dualF U I).map f.op)).X (t + 1) ⟶ T}
        (h₁ : (mappingCocone.inl ((dualF U I).map f.op)).v (t + 1) (t + 1) (by omega) ≫ a =
          (mappingCocone.inl ((dualF U I).map f.op)).v (t + 1) (t + 1) (by omega) ≫ b)
        (h₂ : (mappingCocone.inr ((dualF U I).map f.op)).1.v t (t + 1) rfl ≫ a =
          (mappingCocone.inr ((dualF U I).map f.op)).1.v t (t + 1) rfl ≫ b) :
        a = b := by
      rw [← Category.id_comp a, ← mappingCocone.id_X _ (t + 1) t (by omega)]
      simp only [Preadditive.add_comp, Category.assoc, h₁, h₂]
      rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
        mappingCocone.id_X, Category.id_comp]
    refine hext ?_ ?_
    · erw [← Category.assoc, ordinaryConeComparison_inl]
      dsimp only [g]
      erw [Preadditive.comp_add, Linear.comp_units_smul]
      simp only [← Category.assoc, inB_outB, inB_outA, zero_comp,
        Category.id_comp, smul_zero, add_zero, Category.comp_id]
    · erw [← Category.assoc, ordinaryConeComparison_inr]
      dsimp only [g]
      erw [Linear.units_smul_comp, Preadditive.comp_add, Linear.comp_units_smul]
      simp only [← Category.assoc, inA_outA, inA_outB, zero_comp,
        zero_add, Category.id_comp, smul_smul, Int.units_mul_self, one_smul,
        Category.comp_id]
  · dsimp only [g]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
    erw [ordinaryConeComparison_inl, ordinaryConeComparison_inr,
      Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
    exact out_in_sum P I f t

private theorem cocone_ext {K L : CochainComplex A ℤ} (g : K ⟶ L)
    (t : ℤ) {T : A} {a b : (mappingCocone g).X (t + 1) ⟶ T}
    (h₁ : (mappingCocone.inl g).v (t + 1) (t + 1) (by omega) ≫ a =
      (mappingCocone.inl g).v (t + 1) (t + 1) (by omega) ≫ b)
    (h₂ : (mappingCocone.inr g).1.v t (t + 1) rfl ≫ a =
      (mappingCocone.inr g).1.v t (t + 1) rfl ≫ b) : a = b := by
  rw [← Category.id_comp a, ← mappingCocone.id_X g (t + 1) t (by omega)]
  simp only [Preadditive.add_comp, Category.assoc, h₁, h₂]
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
    mappingCocone.id_X, Category.id_comp]

private theorem ordinaryConeComparison_fst {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    ordinaryConeComparison P I f ≫ (dualF U I).map (mappingCone.inr f).op =
      mappingCocone.fst ((dualF U I).map f.op) := by
  apply HomologicalComplex.hom_ext
  intro q
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, q = t + 1 := ⟨q - 1, by omega⟩
  change (ordinaryConeComparison P I f).f (t + 1) ≫ outB P I f (t + 1) = _
  refine cocone_ext ((dualF U I).map f.op) t ?_ ?_
  · erw [← Category.assoc, ordinaryConeComparison_inl, inB_outB,
      mappingCocone.inl_v_fst_f]
  · erw [← Category.assoc, ordinaryConeComparison_inr, Linear.units_smul_comp,
      inA_outB, smul_zero, mappingCocone.inr_v_fst_f]

private theorem ordinaryConeComparison_boundary {H : HomData A} (P : Spec H U)
    (I : CochainComplex A ℤ) {E G : CochainComplex A ℤ} (f : E ⟶ G) :
    (mappingCocone.triangle ((dualF U I).map f.op)).mor₃ ≫
      (ordinaryConeComparison P I f)⟦(1 : ℤ)⟧' =
        ((coneBeta P I f).rightShift 1 0 (zero_add 1)).homOf := by
  apply HomologicalComplex.hom_ext
  intro q
  dsimp only [mappingCocone.triangle, mappingCone.triangle, Pretriangulated.Triangle.mk,
    HomologicalComplex.comp_f]
  rw [CochainComplex.shiftFunctor_map_f']
  simp only [Cocycle.homOf_f, Cocycle.rightShift_coe]
  rw [Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) (q + 1) rfl]
  simp only [Category.assoc]
  change (mappingCone.inr ((dualF U I).map f.op)).f q ≫
      ((shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by omega)).inv.app
        (mappingCone ((dualF U I).map f.op))).f q ≫
      (ordinaryConeComparison P I f).f (q + 1) = _
  have h : (mappingCone.inr ((dualF U I).map f.op)).f q ≫
        ((shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) 1 (by omega)).inv.app
        (mappingCone ((dualF U I).map f.op))).f q =
      (mappingCocone.inr ((dualF U I).map f.op)).1.v q (q + 1) rfl := by
    simp [mappingCocone.inr, Cocycle.rightShift_coe, Cochain.rightShift_v,
      shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_inv_app_f',
      CochainComplex.shiftFunctorZero_hom_app_f,
      CochainComplex.shiftFunctorAdd'_hom_app_f',
      CochainComplex.shiftFunctorZero_inv_app_f]
    rfl
  erw [← Category.assoc, h, ordinaryConeComparison_inr]
  simp only [coneBeta, Cocycle.mk_coe, coneBetaCochain_v,
    CochainComplex.shiftFunctorObjXIso, eqToIso_refl, Iso.refl_inv, Category.comp_id]
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id]

private theorem fstX_reindex {E G : CochainComplex A ℤ} (f : E ⟶ G)
    (i j k : ℤ) (h : i + 1 = j) (h' : j = k) :
    HomologicalComplex.homotopyCofiber.fstX f i j h ≫ (E.XIsoOfEq h').hom =
      HomologicalComplex.homotopyCofiber.fstX f i k (h.trans h') := by
  subst k
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

private abbrev oppositeConeTriangle {E G : CochainComplex A ℤ} (f : E ⟶ G) :=
  (Pretriangulated.triangleOpEquivalence (CochainComplex A ℤ)).functor.obj
    (op (CochainComplex.mappingCone.triangle f))

private theorem oppositeConeBoundary_f {E G : CochainComplex A ℤ}
    (f : E ⟶ G) (p : ℤ) :
    ((oppositeConeTriangle f).mor₃.unop).f p =
      -HomologicalComplex.homotopyCofiber.fstX f (p + -1) p (by change p + -1 + 1 = p; omega) := by
  dsimp only [oppositeConeTriangle, Pretriangulated.triangleOpEquivalence,
    Pretriangulated.TriangleOpEquivalence.functor, Pretriangulated.Triangle.mk]
  rw [unop_comp]
  simp only [Pretriangulated.shiftFunctor_op_map _ 1 (-1) (by omega),
    shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Quiver.Hom.unop_op]
  dsimp only [opShiftFunctorEquivalence, shiftFunctorOpIso]
  simp only [unop_comp, Quiver.Hom.unop_op, Category.comp_id,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.comp_id, NatIso.op_inv, Iso.symm_inv, NatTrans.op_app,
    Quiver.Hom.unop_op, HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    SignedDoubleHomCone.Calculation.triangle_f, shiftFunctorCompIsoId,
    CochainComplex.shiftFunctorAdd'_hom_app_f', CochainComplex.shiftFunctorZero_inv_app_f]
  simp only [Category.comp_id, unop_comp, Quiver.Hom.unop_op,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctor_map_f', SignedDoubleHomCone.Calculation.triangle_f,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorZero_hom_app_f,
    CochainComplex.shiftFunctorZero_inv_app_f]
  simp only [unop_id, HomologicalComplex.id_f, Category.id_comp, Category.comp_id,
    Category.assoc, Preadditive.neg_comp,
    HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    SignedDoubleHomCone.Calculation.fstX_reindex]
  change 𝟙 _ ≫ (-HomologicalComplex.homotopyCofiber.fstX f
    (p + -1) (p + -1 + 1) rfl ≫ 𝟙 _ ≫ 𝟙 _ ≫
      (E.XIsoOfEq (show p + -1 + 1 = p by omega)).hom ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id, Category.assoc, Preadditive.neg_comp,
    SignedDoubleHomCone.Calculation.fstX_reindex]

end CategoryTheory.SignedDoubleHomCone.Calculation

/- The checked ordinary stage uses the naive opposite shift on its source and the negative
pullback shift on its target. Thus its parameter m is the original complex shift. The correction
is m(m-1)/2; after setting m=-n for the triangulated opposite this becomes n(n+1)/2.
The remaining private helpers identify the signed image of a reversed cone triangle with
a mapping-cocone triangle, then descend this calculation through localization. -/
namespace CategoryTheory.RingedHomUniverses
private abbrev negInt : ℤ →+ ℤ := AddMonoidHom.mk' (fun n : ℤ ↦ -n) (by intros; lia)
private theorem negativeShift_add_hom_generic {B : Type*} [Category B] [HasShift B ℤ]
    (X : B) (a b : ℤ) :
    (shiftFunctorAdd (PullbackShift B negInt) a b).hom.app X =
      (shiftFunctorAdd' B (-a) (-b) (-(a + b)) (by omega)).hom.app X := by
  rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
  rw [pullbackShiftFunctorAdd'_hom_app negInt X a b (a + b) rfl
    (-a) (-b) (-(a + b)) rfl rfl rfl]
  simp only [pullbackShiftIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp]
  erw [Functor.map_id, Category.comp_id, Category.comp_id]

private theorem negativeShift_isoAdd_inv_app
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (F : OppositeShift A ℤ ⥤ PullbackShift B negInt) (a b : ℤ)
    (ea : shiftFunctor _ a ⋙ F ≅ F ⋙ shiftFunctor _ a)
    (eb : shiftFunctor _ b ⋙ F ≅ F ⋙ shiftFunctor _ b) (E : A) :
    (Functor.CommShift.isoAdd ea eb).inv.app (op E) =
      (shiftFunctorAdd' B (-a) (-b) (-(a + b)) (by omega)).hom.app (F.obj (op E)) ≫
        (shiftFunctor B (-b)).map (ea.inv.app (op E)) ≫
          eb.inv.app (op (E⟦a⟧)) ≫ F.map (((shiftFunctorAdd A a b).hom.app E).op) := by
  rw [Functor.CommShift.isoAdd_inv_app, negativeShift_add_hom_generic,
    oppositeShiftFunctorAdd_inv_app]
  rfl

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{max c v r})
attribute [local semireducible] CategoryTheory.homComplexFunctor
private def ordinaryDual (I : Complex.{c, v, r} J R) :
    OppositeShift (Complex.{c, v, r} J R) ℤ ⥤
      PullbackShift (Complex.{c, v, r} J R) negInt where
  obj E := complexHom.{c, v, r} J R E.unop I
  map f := (homComplexFunctor.{c, v, max c v r, max c v r} (R := R).map f).app I
  map_id E := by
    simp only [Functor.map_id, NatTrans.id_app]
    rfl
  map_comp f g := by simp only [Functor.map_comp, NatTrans.comp_app]
attribute [local irreducible] CategoryTheory.homComplexFunctor
private def rawSourceIso (I : Complex.{c, v, r} J R) (n : ℤ) :
    shiftFunctor _ n ⋙ ordinaryDual.{c, v, r} J R I ≅
      ordinaryDual.{c, v, r} J R I ⋙ shiftFunctor _ n := by
  let e := (ordinaryLeftShift.{c, v, r} J R n).choose
  refine NatIso.ofComponents (fun X ↦ e.symm.app (X, I)) ?_
  intro X Y f
  change (homComplexFunctor.{c, v, max c v r, max c v r} (R := R).map
      (((shiftFunctor (Complex.{c, v, r} J R) n).map f.unop).op)).app I ≫
        e.inv.app (Y, I) = e.inv.app (X, I) ≫
          (shiftFunctor (Complex.{c, v, r} J R) (-n)).map
            ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R).map f).app I)
  simpa only [ordinaryDual, ordinaryBifunctor, Functor.uncurry_obj_map,
    Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id, negInt,
    Functor.comp_map, Functor.comp_obj, Functor.op_map,
    Functor.prod_map, Functor.prod_obj, Functor.id_map, Functor.id_obj,
    Prod.sectL_map, Prod.sectL_obj, Iso.app_hom, Iso.symm_hom] using
      e.inv.naturality (Prod.mkHom f (𝟙 I))
private theorem rawSourceIso_formula (I E : Complex.{c, v, r} J R) (n k p q : ℤ)
    (h : p + k = q) :
    (((rawSourceIso.{c, v, r} J R I n).inv.app (op E)).f k) ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h =
      (n * k).negOnePow •
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I (k + -n)
          (p + n) q (by omega) := by
  change (((ordinaryLeftShift.{c, v, r} J R n).choose.hom.app (op E, I)).f k) ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h = _
  simpa only [Iso.app_hom] using
    (ordinaryLeftShift.{c, v, r} J R n).choose_spec E I k p q h
private def correctedSourceIso (I : Complex.{c, v, r} J R) (n : ℤ) :
    shiftFunctor _ n ⋙ ordinaryDual.{c, v, r} J R I ≅
      ordinaryDual.{c, v, r} J R I ⋙ shiftFunctor _ n :=
  (n * (n - 1) / 2).negOnePow • rawSourceIso.{c, v, r} J R I n
private theorem units_smul_f (E F : Complex.{c, v, r} J R)
    (u : ℤˣ) (f : E ⟶ F) (k : ℤ) : (u • f).f k = u • f.f k := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, HomologicalComplex.neg_f_apply]
private theorem correctedSourceIso_formula (I E : Complex.{c, v, r} J R)
    (n k p q : ℤ) (h : p + k = q) :
    (((correctedSourceIso.{c, v, r} J R I n).inv.app (op E)).f k) ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h =
      (n * (n - 1) / 2 + n * k).negOnePow •
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I (k + -n)
          (p + n) q (by omega) := by
  simp only [correctedSourceIso, Preadditive.smul_iso_inv,
    Int.units_inv_eq_self, NatTrans.app_units_zsmul]
  change (((n * (n - 1) / 2).negOnePow •
      ((rawSourceIso.{c, v, r} J R I n).inv.app (op E) :
        (complexHom.{c, v, r} J R E I)⟦-n⟧ ⟶ complexHom.{c, v, r} J R (E⟦n⟧) I)).f k) ≫
          homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦n⟧) I k p q h = _
  erw [units_smul_f.{c, v, r} J R, Linear.units_smul_comp, rawSourceIso_formula]
  rw [smul_smul, ← Int.negOnePow_add]
private theorem ordinaryDual_map_formula (I E F : Complex.{c, v, r} J R)
    (f : F ⟶ E) (k p q : ℤ) (h : p + k = q) :
    ((ordinaryDual.{c, v, r} J R I).map f.op).f k ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) F I k p q h =
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I k p q h ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R)
            (f.f p) (𝟙 _) := by
  have hh := homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} f (𝟙 I) k p q h
  simpa only [ordinaryDual, Functor.comp_map, Prod.sectL_map,
    Functor.uncurry_obj_map, Prod.sectL_obj, Functor.map_id, NatTrans.id_app, Category.comp_id,
    HomologicalComplex.id_f] using hh
private theorem negativeShift_zero_hom (E : Complex.{c, v, r} J R) :
    (shiftFunctorZero (PullbackShift (Complex.{c, v, r} J R) negInt) ℤ).hom.app E =
      (shiftFunctorZero (Complex.{c, v, r} J R) ℤ).hom.app E := by
  rw [pullbackShiftFunctorZero_hom_app]
  simp only [pullbackShiftIso, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
private theorem sourceProjection_eq (I E : Complex.{c, v, r} J R)
    (k k' p p' q : ℤ) (hk : k = k') (hp : p = p')
    (h : p + k = q) (h' : p' + k' = q) :
    ((complexHom.{c, v, r} J R E I).XIsoOfEq hk).hom ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) E I k' p' q h' ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R)
            (E.XIsoOfEq hp).hom (𝟙 _) =
      homComplexπ.{c, v, max c v r, max c v r} (R := R) E I k p q h := by
  subst k' p'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    SheafOfModules.homObjMap_id, Category.id_comp, Category.comp_id]
private theorem correctedSourceIso_zero (I : Complex.{c, v, r} J R) :
    correctedSourceIso.{c, v, r} J R I 0 =
      Functor.CommShift.isoZero (ordinaryDual.{c, v, r} J R I) ℤ := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext E
  apply HomologicalComplex.hom_ext
  intro k
  apply Fan.IsLimit.hom_ext
    (homComplexIsLimit.{c, v, max c v r, max c v r} (E.unop⟦(0 : ℤ)⟧) I k)
  intro p
  rw [Functor.CommShift.isoZero_inv_app]
  dsimp only [Fan.mk_π_app, Fan.proj, HomologicalComplex.comp_f]
  change ((correctedSourceIso.{c, v, r} J R I 0).inv.app E).f k ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) (E.unop⟦(0 : ℤ)⟧) I
        k p (p + k) rfl = _
  erw [correctedSourceIso_formula.{c, v, r} J R I E.unop 0 k p (p + k) rfl]
  rw [negativeShift_zero_hom, oppositeShiftFunctorZero_inv_app]
  change _ = (((shiftFunctorZero (Complex.{c, v, r} J R) ℤ).hom.app
      (complexHom.{c, v, r} J R E.unop I)).f k) ≫
        (((ordinaryDual.{c, v, r} J R I).map
          (((shiftFunctorZero (Complex.{c, v, r} J R) ℤ).hom.app E.unop).op)).f k) ≫
            homComplexπ.{c, v, max c v r, max c v r} (R := R)
              (E.unop⟦(0 : ℤ)⟧) I k p (p + k) rfl
  erw [ordinaryDual_map_formula.{c, v, r} J R]
  simp only [CochainComplex.shiftFunctorZero_hom_app_f,
    zero_mul, Int.zero_ediv, zero_add, Int.negOnePow_zero, one_smul, Functor.id_obj]
  exact (sourceProjection_eq.{c, v, r} J R I E.unop (k + -0) k (p + 0) p (p + k)
    (by omega) (by omega) (by omega) rfl).symm
private theorem correction_add (a b : ℤ) :
    (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  have he (n : ℤ) : 2 ∣ n * (n - 1) := by
    have h := Int.two_dvd_mul_add_one (n - 1)
    convert h using 1
    ring
  have ha := Int.ediv_mul_cancel (he a)
  have hb := Int.ediv_mul_cancel (he b)
  have hab := Int.ediv_mul_cancel (he (a + b))
  have h : (a + b) * (a + b - 1) = a * (a - 1) + b * (b - 1) + 2 * (a * b) := by ring
  omega
private theorem correctionSign_add (a b k : ℤ) :
    ((a + b) * (a + b - 1) / 2 + (a + b) * k).negOnePow =
      (b * (b - 1) / 2 + b * k).negOnePow *
        (a * (a - 1) / 2 + a * (k + -b)).negOnePow := by
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff, correction_add]
  refine ⟨a * b, ?_⟩
  ring
private theorem correctedSourceIso_add (I : Complex.{c, v, r} J R) (a b : ℤ) :
    correctedSourceIso.{c, v, r} J R I (a + b) =
      Functor.CommShift.isoAdd (correctedSourceIso.{c, v, r} J R I a)
        (correctedSourceIso.{c, v, r} J R I b) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext E
  have hadd := negativeShift_isoAdd_inv_app
    (A := Complex.{c, v, r} J R) (B := Complex.{c, v, r} J R)
    (ordinaryDual.{c, v, r} J R I) a b
    (correctedSourceIso.{c, v, r} J R I a) (correctedSourceIso.{c, v, r} J R I b) E.unop
  erw [hadd]
  apply HomologicalComplex.hom_ext
  intro k
  apply Fan.IsLimit.hom_ext
    (homComplexIsLimit.{c, v, max c v r, max c v r} (E.unop⟦a + b⟧) I k)
  intro p
  dsimp only [Fan.mk_π_app, Fan.proj, HomologicalComplex.comp_f]
  simp only [Category.assoc]
  change ((correctedSourceIso.{c, v, r} J R I (a + b)).inv.app E).f k ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) (E.unop⟦a + b⟧) I
        k p (p + k) rfl = _
  erw [correctedSourceIso_formula.{c, v, r} J R I E.unop (a + b) k p (p + k) rfl]
  have hm := ordinaryDual_map_formula.{c, v, r} J R I
    ((E.unop⟦a⟧)⟦b⟧) (E.unop⟦a + b⟧)
    ((shiftFunctorAdd (Complex.{c, v, r} J R) a b).hom.app E.unop) k p (p + k) rfl
  erw [hm]
  have hb := correctedSourceIso_formula.{c, v, r} J R I (E.unop⟦a⟧) b
    k p (p + k) rfl
  rw [reassoc_of% hb]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp]
  rw [CochainComplex.shiftFunctor_map_f']
  have ha := correctedSourceIso_formula.{c, v, r} J R I E.unop a
    (k + -b) (p + b) (p + k) (by omega)
  erw [reassoc_of% ha]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
  simp only [CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctorAdd_hom_app_f]
  erw [sourceProjection_eq.{c, v, r} J R I E.unop
    (k + -(a + b)) (k + -b + -a) (p + (a + b)) (p + b + a) (p + k)
    (by omega) (by omega) (by omega) (by omega)]
  rw [correctionSign_add]

@[instance_reducible]
private def ordinarySignedCommShift (I : Complex.{c, v, r} J R) :
    (ordinaryDual.{c, v, r} J R I).CommShift ℤ where
  commShiftIso := correctedSourceIso.{c, v, r} J R I
  commShiftIso_zero := correctedSourceIso_zero.{c, v, r} J R I
  commShiftIso_add := correctedSourceIso_add.{c, v, r} J R I
private theorem contravariantComparison_shift
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (F : Aᵒᵖ ⥤ A) [F.CommShift ℤ]
    (T : Bᵒᵖ ⥤ B) [T.CommShift ℤ] (e : F ⋙ Q ≅ Q.op ⋙ T)
    [NatTrans.CommShift e.hom ℤ] (E : A) (X : B) (eX : Q.obj E ≅ X) (n : ℤ) :
    Q.map ((F.commShiftIso n).hom.app (op E)) ≫
      (Q.commShiftIso n).hom.app (F.obj (op E)) ≫
        (e.hom.app (op E) ≫ T.map eX.inv.op)⟦n⟧' =
    e.hom.app (op (E⟦-n⟧)) ≫
      T.map (((shiftFunctor B (-n)).map eX.inv ≫
        (Q.commShiftIso (-n)).inv.app E).op) ≫
          (T.commShiftIso n).hom.app (op X) := by
  have hh := NatTrans.shift_app_comm e.hom n (op E)
  have hn := (T.commShiftIso n).hom.naturality eX.inv.op
  have hhm := congrArg (fun z ↦ z ≫ (T.map eX.inv.op)⟦n⟧') hh
  rw [Functor.commShiftIso_comp_hom_app F Q,
    Functor.commShiftIso_comp_hom_app Q.op T] at hhm
  simp only [Category.assoc] at hhm
  dsimp only [Functor.comp_map] at hn
  erw [← hn] at hhm
  simp only [Functor.op_commShiftIso_hom_app Q (op E) n (-n) (by omega),
    shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    unop_id, Functor.map_id, op_id, Category.id_comp, Category.comp_id] at hhm
  simp only [Functor.op_map, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Pretriangulated.shiftFunctor_op_map eX.inv.op n (-n) (by omega),
    shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Quiver.Hom.unop_op, ← op_comp] at hhm
  erw [Functor.map_id, op_id, Category.id_comp, Category.id_comp, Category.comp_id] at hhm
  simp only [← op_comp] at hhm
  convert hhm using 1 <;> rfl

private theorem hom_eq_neg_of_comparison {A : Type*} [Category A] [Preadditive A]
    {U V W : A} {a : U ⟶ V} [IsIso a] {t : V ⟶ W} {s : W ⟶ V}
    {r : V ⟶ W} [IsIso s] (h : -a = a ≫ t ≫ s) (hr : r ≫ s = 𝟙 V) : t = -r := by
  rw [← cancel_mono s, Preadditive.neg_comp, hr]
  apply (cancel_epi a).mp
  simpa only [Category.assoc, Preadditive.comp_neg, Category.comp_id] using h.symm

private theorem inv_eq_of_comparison {A : Type*} [Category A]
    {U V W : A} {a : U ⟶ V} [IsIso a] {t : V ⟶ W} [IsIso t]
    {r s : W ⟶ V} (h : a = a ≫ t ≫ s) (hr : t ≫ r = 𝟙 V) : r = s := by
  rw [← cancel_epi t, hr]
  apply (cancel_epi a).mp
  simpa only [Category.assoc, Category.comp_id] using h

private theorem negative_normalization_of_comparisons
    {A : Type*} [Category A] [Preadditive A] {U V W Z : A}
    {r : U ⟶ V} {ri : V ⟶ U} {b : V ⟶ W} {a : U ⟶ Z} [IsIso a]
    {t : Z ⟶ W} {s : W ⟶ Z} {si : Z ⟶ W} [IsIso s]
    (hn : b ≫ s = ri ≫ a) (hc : (-r) ≫ b = a ≫ t)
    (hr : r ≫ ri = 𝟙 U) (hs : si ≫ s = 𝟙 Z) : t = -si := by
  apply hom_eq_neg_of_comparison (a := a) ?_ hs
  have h := congrArg (fun z ↦ z ≫ s) hc
  simp only [Category.assoc, Preadditive.neg_comp] at h
  rw [hn] at h
  simpa only [← Category.assoc, hr, Category.id_comp] using h

private theorem positive_normalization_of_comparisons
    {A : Type*} [Category A] {U V W Z : A}
    {r : U ⟶ V} {ri : V ⟶ U} {b : V ⟶ W} {a : U ⟶ Z} [IsIso a]
    {t : Z ⟶ W} [IsIso t] {ti s : W ⟶ Z}
    (hn : b ≫ s = ri ≫ a) (hc : r ≫ b = a ≫ t)
    (hr : r ≫ ri = 𝟙 U) (ht : t ≫ ti = 𝟙 Z) : ti = s := by
  apply inv_eq_of_comparison (a := a) ?_ ht
  have h := congrArg (fun z ↦ z ≫ s) hc
  simp only [Category.assoc] at h
  rw [hn] at h
  simpa only [← Category.assoc, hr, Category.id_comp] using h

private abbrev undoNegativeShift {A : Type*} [Category A] [HasShift A ℤ] :
    PullbackShift (PullbackShift A negInt) negInt ⥤ A := 𝟭 A

private def undoNegativeShiftIso {A : Type*} [Category A] [HasShift A ℤ] (n : ℤ) :
    shiftFunctor _ n ⋙ (undoNegativeShift (A := A)) ≅
      undoNegativeShift ⋙ shiftFunctor _ n :=
  (Functor.rightUnitor _) ≪≫
    pullbackShiftIso (PullbackShift A negInt) negInt n (-n) rfl ≪≫
    pullbackShiftIso A negInt (-n) n (by dsimp [negInt]; omega) ≪≫
    (Functor.leftUnitor _).symm

private instance undoNegativeShiftCommShift {A : Type*} [Category A] [HasShift A ℤ] :
    (undoNegativeShift (A := A)).CommShift ℤ where
  commShiftIso := undoNegativeShiftIso
  commShiftIso_zero := by
    ext X
    simp only [undoNegativeShiftIso, Functor.CommShift.isoZero_hom_app,
      Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id]
    change _ = (shiftFunctorZero (PullbackShift (PullbackShift A negInt) negInt) ℤ).hom.app X ≫
      (shiftFunctorZero A ℤ).inv.app X
    rw [pullbackShiftFunctorZero_hom_app (C := PullbackShift A negInt),
      pullbackShiftFunctorZero_hom_app (C := A)]
    simp only [pullbackShiftIso, negInt, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app]
    rfl
  commShiftIso_add a b := by
    ext X
    simp only [undoNegativeShiftIso, Functor.CommShift.isoAdd_hom_app,
      Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id]
    change _ =
      (shiftFunctorAdd (PullbackShift (PullbackShift A negInt) negInt) a b).hom.app X ≫
        _ ≫ _ ≫ (shiftFunctorAdd A a b).inv.app X
    have hadd := pullbackShiftFunctorAdd'_hom_app (C := A) negInt
      (show PullbackShift A negInt from X) (-a) (-b) (-(a + b)) (by omega)
      a b (a + b) (by dsimp [negInt]; omega) (by dsimp [negInt]; omega)
      (by dsimp [negInt]; omega)
    rw [← shiftFunctorAdd'_eq_shiftFunctorAdd,
      pullbackShiftFunctorAdd'_hom_app (C := PullbackShift A negInt) negInt X
        a b (a + b) rfl (-a) (-b) (-(a + b)) rfl rfl rfl]
    erw [hadd]
    have ho (n : ℤ) :
        pullbackShiftIso (PullbackShift A negInt) negInt n (-n) rfl = Iso.refl _ := rfl
    simp only [ho, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.assoc]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
    let e (n : ℤ) : shiftFunctor A (- -n) ≅ shiftFunctor A n :=
      pullbackShiftIso A negInt (-n) n (by dsimp [negInt]; omega)
    change (𝟙 _ ≫ 𝟙 _ ≫ (e (a + b)).hom.app X :
        (shiftFunctor A (- -(a + b))).obj X ⟶ (shiftFunctor A (a + b)).obj X) =
      𝟙 _ ≫ (e (a + b)).hom.app X ≫ (shiftFunctorAdd A a b).hom.app X ≫
        (e b).inv.app ((shiftFunctor A a).obj X) ≫
          (shiftFunctor A (- -b)).map ((e a).inv.app X) ≫
            𝟙 _ ≫ (shiftFunctor A (- -b)).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫
              (e b).hom.app ((shiftFunctor A (- -a)).obj X) ≫
                (shiftFunctor A b).map (𝟙 _ ≫ 𝟙 _ ≫ (e a).hom.app X) ≫
                  (shiftFunctorAdd A a b).inv.app X
    simp only [Functor.map_id, Category.id_comp]
    rw [(e b).hom.naturality_assoc]
    simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc, Category.comp_id]
    rw [Iso.hom_inv_id_app, Category.comp_id]

private abbrev convertedDual {A B : Type*} [Category A] [Category B]
    [HasShift A ℤ] [HasShift B ℤ]
    (F : OppositeShift A ℤ ⥤ PullbackShift B negInt) : Aᵒᵖ ⥤ B :=
  PullbackShift.functor negInt F ⋙ undoNegativeShift

@[instance_reducible]
private def convertedDualCommShift {A B : Type*} [Category A] [Category B]
    [HasShift A ℤ] [HasShift B ℤ]
    (F : OppositeShift A ℤ ⥤ PullbackShift B negInt) [F.CommShift ℤ] :
    (convertedDual F).CommShift ℤ :=
  Functor.CommShift.comp (A := ℤ) (PullbackShift.functor negInt F) undoNegativeShift

/- Keep the change of shift conventions abstract, before specializing to sheaf complexes. -/
private theorem convertedDualCommShift_one {A B : Type*} [Category A] [Category B]
    [HasShift A ℤ] [HasShift B ℤ]
    (F : OppositeShift A ℤ ⥤ PullbackShift B negInt) [F.CommShift ℤ] (E : Aᵒᵖ) :
    ((convertedDualCommShift F).commShiftIso (1 : ℤ)).hom.app E =
      (F.commShiftIso (-1 : ℤ)).hom.app E := by
  dsimp only [convertedDualCommShift, Functor.CommShift.comp, Functor.commShiftPullback,
    Functor.commShiftIso, undoNegativeShiftCommShift, undoNegativeShiftIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, pullbackShiftIso,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    undoNegativeShift, Functor.id_map, Functor.map_id]
  change (𝟙 _ ≫ (𝟙 _ ≫ (F.commShiftIso (-1 : ℤ)).hom.app E ≫ 𝟙 _) ≫
    𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ :
      F.obj ((shiftFunctor A (-1 : ℤ)).op.obj E) ⟶ (shiftFunctor B (1 : ℤ)).obj (F.obj E)) = _
  simp only [Category.id_comp, Category.comp_id]

private theorem convertedDualCommShift_neg_one {A B : Type*} [Category A] [Category B]
    [HasShift A ℤ] [HasShift B ℤ]
    (F : OppositeShift A ℤ ⥤ PullbackShift B negInt) [F.CommShift ℤ] (E : Aᵒᵖ) :
    ((convertedDualCommShift F).commShiftIso (-1 : ℤ)).hom.app E =
      (F.commShiftIso (1 : ℤ)).hom.app E := by
  dsimp only [convertedDualCommShift, Functor.CommShift.comp, Functor.commShiftPullback,
    Functor.commShiftIso, undoNegativeShiftCommShift, undoNegativeShiftIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, pullbackShiftIso,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    undoNegativeShift, Functor.id_map, Functor.map_id]
  change (𝟙 _ ≫ (𝟙 _ ≫ (F.commShiftIso (1 : ℤ)).hom.app E ≫ 𝟙 _) ≫
    𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ :
      F.obj ((shiftFunctor A (1 : ℤ)).op.obj E) ⟶ (shiftFunctor B (-1)).obj (F.obj E)) = _
  simp only [Category.id_comp, Category.comp_id]

private abbrev triangulatedOrdinaryDual (I : Complex.{c, v, r} J R) :
    (Complex.{c, v, r} J R)ᵒᵖ ⥤ Complex.{c, v, r} J R :=
  convertedDual (A := Complex.{c, v, r} J R) (B := Complex.{c, v, r} J R)
    (ordinaryDual.{c, v, r} J R I)

@[instance_reducible]
private def triangulatedOrdinaryCommShift (I : Complex.{c, v, r} J R) :
    (triangulatedOrdinaryDual.{c, v, r} J R I).CommShift ℤ :=
  letI := ordinarySignedCommShift.{c, v, r} J R I
  convertedDualCommShift (A := Complex.{c, v, r} J R) (B := Complex.{c, v, r} J R)
    (ordinaryDual.{c, v, r} J R I)

attribute [local instance] triangulatedOrdinaryCommShift

private theorem triangulatedOrdinaryCommShift_one (I E : Complex.{c, v, r} J R) :
    ((triangulatedOrdinaryDual.{c, v, r} J R I).commShiftIso (1 : ℤ)).hom.app (op E) =
      -(rawSourceIso.{c, v, r} J R I (-1)).hom.app (op E) := by
  letI := ordinarySignedCommShift.{c, v, r} J R I
  change ((convertedDualCommShift (A := Complex.{c, v, r} J R)
    (B := Complex.{c, v, r} J R) (ordinaryDual.{c, v, r} J R I)).commShiftIso
    (1 : ℤ)).hom.app (op E) = _
  rw [convertedDualCommShift_one]
  change ((1 : ℤ).negOnePow • rawSourceIso.{c, v, r} J R I (-1)).hom.app (op E) = _
  simp only [Preadditive.smul_iso_hom, NatTrans.app_units_zsmul,
    Int.negOnePow_one, Units.neg_smul, one_smul, NatTrans.app_neg]

private theorem triangulatedOrdinaryCommShift_neg_one (I E : Complex.{c, v, r} J R) :
    ((triangulatedOrdinaryDual.{c, v, r} J R I).commShiftIso (-1 : ℤ)).hom.app (op E) =
      (rawSourceIso.{c, v, r} J R I 1).hom.app (op E) := by
  letI := ordinarySignedCommShift.{c, v, r} J R I
  change ((convertedDualCommShift (A := Complex.{c, v, r} J R)
    (B := Complex.{c, v, r} J R) (ordinaryDual.{c, v, r} J R I)).commShiftIso
    (-1 : ℤ)).hom.app (op E) = _
  rw [convertedDualCommShift_neg_one]
  change ((0 : ℤ).negOnePow • rawSourceIso.{c, v, r} J R I 1).hom.app (op E) = _
  simp only [Preadditive.smul_iso_hom, NatTrans.app_units_zsmul,
    Int.negOnePow_zero, one_smul]

private instance ordinaryModuleBinaryBiproducts :
    HasBinaryBiproducts (Modules.{c, v, r} J R) :=
  SignedDoubleHomCone.moduleBinaryBiproducts.{c, v, r, max c v r} (R := R)

private def internalHomData : SignedDoubleHomCone.Calculation.HomData
    (Modules.{c, v, r} J R) where
  obj := SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R)
  map := fun f g ↦ SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f g
  map_id := fun _ _ ↦ SheafOfModules.homObjMap_id.{max c v r, v, c, max c v r}
  map_comp := fun f f' g g' ↦ SheafOfModules.homObjMap_comp_homObjMap f f' g g'
  map_add_left := fun f g h ↦ SignedDoubleHomCone.map_add_left.{c, v, r, max c v r} (R := R) f g h
  map_zero_left := fun g ↦ SignedDoubleHomCone.map_zero_left.{c, v, r, max c v r} (R := R) g

private def internalHomSpec : SignedDoubleHomCone.Calculation.Spec
    (internalHomData.{c, v, r} J R)
      (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) where
  π := homComplexπ.{c, v, max c v r, max c v r} (R := R)
  lim := fun E I q ↦ homComplexIsLimit.{c, v, max c v r, max c v r} E I q
  diff := homComplex_d_π.{c, v, max c v r, max c v r} (R := R)
  map := fun _ _ _ _ f g n a b h ↦
    homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} f g n a b h

private def internalHomConeIso (I : Complex.{c, v, r} J R)
    {E G : Complex.{c, v, r} J R} (f : E ⟶ G) :
    CochainComplex.mappingCocone ((ordinaryDual.{c, v, r} J R I).map f.op) ≅
      (ordinaryDual.{c, v, r} J R I).obj (op (CochainComplex.mappingCone f)) := by
  letI := SignedDoubleHomCone.Calculation.ordinaryConeComparison_isIso
    (internalHomSpec.{c, v, r} J R) I f
  exact asIso (SignedDoubleHomCone.Calculation.ordinaryConeComparison
    (internalHomSpec.{c, v, r} J R) I f)

private abbrev oppositeConeTriangle {E G : Complex.{c, v, r} J R} (f : E ⟶ G) :=
  SignedDoubleHomCone.Calculation.oppositeConeTriangle f

private theorem internalHomBoundary (I : Complex.{c, v, r} J R)
    {E G : Complex.{c, v, r} J R} (f : E ⟶ G) :
    (triangulatedOrdinaryDual.{c, v, r} J R I).map (oppositeConeTriangle.{c, v, r} J R f).mor₃ ≫
        ((triangulatedOrdinaryDual.{c, v, r} J R I).commShiftIso (1 : ℤ)).hom.app
          (op (CochainComplex.mappingCone f)) =
      ((SignedDoubleHomCone.Calculation.coneBeta (internalHomSpec.{c, v, r} J R) I f).rightShift
        1 0 (zero_add 1)).homOf := by
  let F := triangulatedOrdinaryDual.{c, v, r} J R I
  let K := CochainComplex.mappingCone f
  let b := SignedDoubleHomCone.Calculation.coneBeta (internalHomSpec.{c, v, r} J R) I f
  have he : (F.commShiftIso (1 : ℤ)).app (op K) =
      -(rawSourceIso.{c, v, r} J R I (-1)).app (op K) := by
    apply Iso.ext
    exact triangulatedOrdinaryCommShift_one.{c, v, r} J R I K
  apply (cancel_mono ((F.commShiftIso (1 : ℤ)).inv.app (op K))).mp
  change F.map (oppositeConeTriangle.{c, v, r} J R f).mor₃ ≫
      (F.commShiftIso (1 : ℤ)).hom.app (op K) ≫
        (F.commShiftIso (1 : ℤ)).inv.app (op K) = _
  rw [Iso.hom_inv_id_app]
  erw [Category.comp_id]
  change F.map (oppositeConeTriangle.{c, v, r} J R f).mor₃ =
    ((b.rightShift 1 0 (zero_add 1)).homOf) ≫ ((F.commShiftIso (1 : ℤ)).app (op K)).inv
  rw [he, Preadditive.neg_iso_inv]
  apply HomologicalComplex.hom_ext
  intro k
  apply Fan.IsLimit.hom_ext
    (homComplexIsLimit.{c, v, max c v r, max c v r} (K⟦(-1 : ℤ)⟧) I k)
  intro p
  change ((ordinaryDual.{c, v, r} J R I).map (oppositeConeTriangle.{c, v, r} J R f).mor₃).f k ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) (K⟦(-1 : ℤ)⟧) I
        k p (p + k) rfl = _
  erw [ordinaryDual_map_formula.{c, v, r} J R]
  erw [SignedDoubleHomCone.Calculation.oppositeConeBoundary_f f p]
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply,
    Iso.app_inv, K, Fan.mk_π_app, Fan.proj,
    CochainComplex.mappingCone.triangle, Pretriangulated.Triangle.mk]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
  erw [rawSourceIso_formula.{c, v, r} J R I (CochainComplex.mappingCone f) (-1) k p (p + k) rfl]
  dsimp only [b, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.rightShift_coe]
  rw [CochainComplex.HomComplex.Cochain.rightShift_v _ 1 0 (zero_add 1)
    k k (add_zero k) (k + 1) rfl]
  simp only [SignedDoubleHomCone.Calculation.coneBeta,
    CochainComplex.HomComplex.Cocycle.mk_coe,
    SignedDoubleHomCone.Calculation.coneBetaCochain_v,
    CochainComplex.shiftFunctorObjXIso, eqToIso_refl, Iso.refl_inv,
    Category.comp_id, Linear.units_smul_comp, Linear.comp_units_smul,
    Int.negOnePow_neg, neg_one_mul, Int.reduceNeg]
  erw [SignedDoubleHomCone.Calculation.inA_proj (internalHomSpec.{c, v, r} J R) I f
    k (p + -1) p (p + k) (by omega) (by omega)]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  exact (congrArg (fun z ↦
    homComplexπ.{c, v, max c v r, max c v r} (R := R) E I k p (p + k) rfl ≫ z)
      (SignedDoubleHomCone.Calculation.map_neg_left
        (H := internalHomData.{c, v, r} J R)
        (HomologicalComplex.homotopyCofiber.fstX f (p + -1) p
          (by change p + -1 + 1 = p; omega))
        (𝟙 (I.X (p + k))))).trans (Preadditive.comp_neg _ _)

private def internalHomConeTriangleIso (I : Complex.{c, v, r} J R)
    {E G : Complex.{c, v, r} J R} (f : E ⟶ G) :
    CochainComplex.mappingCocone.triangle ((ordinaryDual.{c, v, r} J R I).map f.op) ≅
      (triangulatedOrdinaryDual.{c, v, r} J R I).mapTriangle.obj
        (oppositeConeTriangle.{c, v, r} J R f) := by
  refine Pretriangulated.Triangle.isoMk _ _ (internalHomConeIso.{c, v, r} J R I f)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change CochainComplex.mappingCocone.fst
        ((ordinaryDual.{c, v, r} J R I).map f.op) ≫ 𝟙 _ =
      (internalHomConeIso.{c, v, r} J R I f).hom ≫
        (ordinaryDual.{c, v, r} J R I).map (CochainComplex.mappingCone.inr f).op
    rw [Category.comp_id]
    exact (SignedDoubleHomCone.Calculation.ordinaryConeComparison_fst
        (internalHomSpec.{c, v, r} J R) I f).symm
  · change (ordinaryDual.{c, v, r} J R I).map f.op ≫ 𝟙 _ =
      𝟙 _ ≫ (ordinaryDual.{c, v, r} J R I).map f.op
    rw [Category.comp_id, Category.id_comp]
  · change (CochainComplex.mappingCocone.triangle
        ((ordinaryDual.{c, v, r} J R I).map f.op)).mor₃ ≫
      (internalHomConeIso.{c, v, r} J R I f).hom⟦(1 : ℤ)⟧' =
        𝟙 _ ≫ _
    rw [Category.id_comp]
    exact (SignedDoubleHomCone.Calculation.ordinaryConeComparison_boundary
      (internalHomSpec.{c, v, r} J R) I f).trans (internalHomBoundary.{c, v, r} J R I f).symm

end CategoryTheory.RingedHomUniverses

namespace CategoryTheory.RingedHomUniverses
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]
attribute [local instance] triangulatedOrdinaryCommShift

private def dualComparison (I : Complex.{c, v, r} J R) [I.IsKInjective]
    (M : D.{c, v, r, w} J R) (eM : DerivedCategory.Q.obj I ≅ M) :
    triangulatedOrdinaryDual.{c, v, r} J R I ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q.op ⋙
        (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R) :=
  NatIso.ofComponents (fun E ↦ by
    have hc := comparison_isIso_of_kInjective.{c, v, r, w} J R E.unop I
    have hm : IsIso ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj E.unop))) eM.hom)) := by
      change IsIso (((derivedInternalHomOfUniverses.{c, v, r, w} J R).mapIso
        ((Iso.refl (op (DerivedCategory.Q.obj E.unop))).prod eM)).hom)
      infer_instance
    exact asIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E.unop I ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (𝟙 _) eM.hom))) (by
    intro E F f
    change DerivedCategory.Q.map ((ordinaryDual.{c, v, r} J R I).map f) ≫
        (ordinaryComparison.{c, v, r, w} J R).app (F, I) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom (𝟙 _) eM.hom) =
      ((ordinaryComparison.{c, v, r, w} J R).app (E, I) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 _) eM.hom)) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom ((DerivedCategory.Q.map f.unop).op) (𝟙 M))
    have hn := (ordinaryComparison.{c, v, r, w} J R).naturality
      (Prod.mkHom f (𝟙 I))
    simp only [Functor.comp_map, Functor.prod_map, Functor.op_map, Functor.map_id,
      ordinaryBifunctor, Functor.uncurry_obj_map, NatTrans.id_app,
      Category.id_comp, Category.comp_id] at hn
    change DerivedCategory.Q.map ((ordinaryDual.{c, v, r} J R I).map f) ≫
        (ordinaryComparison.{c, v, r, w} J R).app (F, I) =
      (ordinaryComparison.{c, v, r, w} J R).app (E, I) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom ((DerivedCategory.Q.map f.unop).op) (𝟙 _)) at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← Functor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id]
    congr 2
    exact congrArg (fun z ↦ Prod.mkHom z eM.hom) (Category.comp_id _))

private theorem dualComparison_shift (I : Complex.{c, v, r} J R) [I.IsKInjective]
    (M : D.{c, v, r, w} J R) (eM : DerivedCategory.Q.obj I ≅ M)
    (S : (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ)
    (hS : letI := S; NatTrans.CommShift (dualComparison.{c, v, r, w} J R I M eM).hom ℤ)
    (X : D.{c, v, r, w} J R) (E : Complex.{c, v, r} J R)
    (eX : DerivedCategory.Q.obj E ≅ X) (n : ℤ) :
    letI := S
    DerivedCategory.Q.map
        (((triangulatedOrdinaryDual.{c, v, r} J R I).commShiftIso n).hom.app (op E)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (complexHom.{c, v, r} J R E I) ≫
        (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E I ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom eX.inv.op eM.hom))⟦n⟧' =
      ringedSiteOrdinaryHomComparison.{c, v, r, w} J R (E⟦-n⟧) I ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (((shiftFunctor _ (-n)).map eX.inv) ≫
            (DerivedCategory.Q.commShiftIso (-n)).inv.app E).op eM.hom) ≫
        ((Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).commShiftIso n).hom.app
          (op X) := by
  letI := S
  letI := hS
  letI : (triangulatedOrdinaryDual.{c, v, r} J R I).CommShift ℤ :=
    triangulatedOrdinaryCommShift.{c, v, r} J R I
  let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
  have hh := contravariantComparison_shift DerivedCategory.Q
    (triangulatedOrdinaryDual.{c, v, r} J R I) T
    (dualComparison.{c, v, r, w} J R I M eM) E X eX n
  dsimp only [dualComparison, NatIso.ofComponents_hom_app, asIso_hom,
    T, Functor.comp_map, Prod.sectL_map] at hh
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    prod_comp, Category.id_comp, Category.comp_id] at hh
  convert hh using 1 <;> rfl

private theorem sourceShift_raw (X M : D.{c, v, r, w} J R)
    (E I : Complex.{c, v, r} J R)
    (eX : DerivedCategory.Q.obj E ≅ X) (eM : DerivedCategory.Q.obj I ≅ M) (s : ℤ) :
    (DerivedCategory.Q.commShiftIso (-s)).hom.app (complexHom.{c, v, r} J R E I) ≫
        (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E I ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom eX.inv.op eM.hom))⟦-s⟧' ≫
        (sourceShift.{c, v, r, w} J R X s).hom.app M =
      DerivedCategory.Q.map ((rawSourceIso.{c, v, r} J R I s).inv.app (op E)) ≫
        ringedSiteOrdinaryHomComparison.{c, v, r, w} J R (E⟦s⟧) I ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (((shiftFunctor _ s).map eX.inv) ≫
            (DerivedCategory.Q.commShiftIso s).inv.app E).op eM.hom) := by
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  obtain ⟨e, he, hh⟩ := (leftShift_existsUnique.{c, v, r, w} J R).exists.choose_spec
    X E I eX s
  have heq := leftFormula_unique.{c, v, r} J R E I s e
    ((ordinaryLeftShift.{c, v, r} J R s).choose.app (op E, I)) he
    ((ordinaryLeftShift.{c, v, r} J R s).choose_spec E I)
  rw [heq] at hh
  have hn := (sourceShift.{c, v, r, w} J R X s).hom.naturality eM.hom
  change (H.map (Prod.mkHom (𝟙 (op X)) eM.hom))⟦-s⟧' ≫
      (sourceShift.{c, v, r, w} J R X s).hom.app M =
    (sourceShift.{c, v, r, w} J R X s).hom.app (DerivedCategory.Q.obj I) ≫
      H.map (Prod.mkHom (𝟙 (op (X⟦s⟧))) eM.hom) at hn
  have hhm := congrArg (fun z ↦ z ≫
    H.map (Prod.mkHom (𝟙 (op (X⟦s⟧))) eM.hom)) hh
  simp only [Category.assoc] at hhm
  erw [← hn] at hhm
  dsimp only [H] at hhm
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp, prod_comp,
    Category.id_comp, Category.comp_id] at hhm
  exact hhm

private theorem dualShiftDescent (I : Complex.{c, v, r} J R) [I.IsKInjective]
    (M : D.{c, v, r, w} J R) (eM : DerivedCategory.Q.obj I ≅ M) :
    let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
    ∃ S : T.CommShift ℤ,
      (fun [_shiftInst : T.CommShift ℤ] ↦
        NatTrans.CommShift (dualComparison.{c, v, r, w} J R I M eM).hom ℤ)
          (_shiftInst := S) := by
  intro T
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (Modules.{c, v, r} J R) (.up ℤ)
  let F := triangulatedOrdinaryDual.{c, v, r} J R I ⋙ Q
  let e := dualComparison.{c, v, r, w} J R I M eM
  let : Localization.Lifting Q.op W.op F T := ⟨e.symm⟩
  let S := Functor.commShiftOfLocalization Q.op W.op ℤ F T
  letI := S
  letI : NatTrans.CommShift e.inv ℤ :=
    inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso Q.op W.op F T).hom ℤ)
  refine ⟨S, ?_⟩
  change NatTrans.CommShift e.hom ℤ
  constructor
  intro a
  ext E
  dsimp
  rw [← cancel_epi (e.inv.app (E⟦a⟧)), e.inv_hom_id_app_assoc,
    ← NatTrans.shift_app_comm_assoc e.inv, ← Functor.map_comp,
    e.inv_hom_id_app, Functor.map_id, Category.comp_id]

private theorem representativeComparison_isIso
    (I : Complex.{c, v, r} J R) [I.IsKInjective]
    (M X : D.{c, v, r, w} J R) (E : Complex.{c, v, r} J R)
    (eM : DerivedCategory.Q.obj I ≅ M) (eX : DerivedCategory.Q.obj E ≅ X) :
    IsIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E I ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom eX.inv.op eM.hom)) := by
  let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
  have hh : IsIso ((dualComparison.{c, v, r, w} J R I M eM).hom.app (op E) ≫
      T.map eX.inv.op) := by
    have : IsIso eX.inv.op := inferInstance
    infer_instance
  dsimp only [dualComparison, NatIso.ofComponents_hom_app, asIso_hom,
    T, Functor.comp_map, Prod.sectL_map] at hh
  simpa only [Category.assoc, ← Functor.map_comp, prod_comp,
    Category.id_comp, Category.comp_id] using hh

private theorem dualShift_normalized (I : Complex.{c, v, r} J R) [I.IsKInjective]
    (M : D.{c, v, r, w} J R) (eM : DerivedCategory.Q.obj I ≅ M)
    (S : (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ)
    (hS : letI := S; NatTrans.CommShift (dualComparison.{c, v, r, w} J R I M eM).hom ℤ) :
    letI := S
    let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
    (∀ X, (T.commShiftIso (1 : ℤ)).hom.app (op X) =
      -(sourceShift.{c, v, r, w} J R X (-1)).inv.app M) ∧
    (∀ X, (T.commShiftIso (-1 : ℤ)).inv.app (op X) =
      (sourceShift.{c, v, r, w} J R X 1).hom.app M) := by
  letI := S
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
  constructor <;> intro X
  · let E : Complex.{c, v, r} J R := Q.objPreimage X
    let eX : Q.obj E ≅ X := Q.objObjPreimageIso X
    let eXS := (Q.commShiftIso (-1 : ℤ)).app E ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso eX
    let A := ringedSiteOrdinaryHomComparison.{c, v, r, w} J R (E⟦(-1 : ℤ)⟧) I ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (((shiftFunctor _ (-1 : ℤ)).map eX.inv) ≫
          (Q.commShiftIso (-1 : ℤ)).inv.app E).op eM.hom)
    letI : IsIso A := by
      convert representativeComparison_isIso.{c, v, r, w} J R I M (X⟦(-1 : ℤ)⟧)
        (E⟦(-1 : ℤ)⟧) eM eXS using 1
      rfl
    have hn := sourceShift_raw.{c, v, r, w} J R X M E I eX eM (-1 : ℤ)
    have hc := dualComparison_shift.{c, v, r, w} J R I M eM S hS X E eX (1 : ℤ)
    rw [triangulatedOrdinaryCommShift_one.{c, v, r}, Functor.map_neg] at hc
    simp only [Int.reduceNeg] at hn hc
    have hn' := (Category.assoc _ _ _).trans hn
    have hc' := hc.trans (Category.assoc _ _ _).symm
    have hr := (Q.mapIso ((rawSourceIso.{c, v, r} J R I (-1 : ℤ)).app (op E))).hom_inv_id
    dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hr
    apply negative_normalization_of_comparisons hn' hc' hr
    exact (sourceShift.{c, v, r, w} J R X (-1)).inv_hom_id_app M
  · let E : Complex.{c, v, r} J R := Q.objPreimage X
    let eX : Q.obj E ≅ X := Q.objObjPreimageIso X
    let eXS := (Q.commShiftIso (1 : ℤ)).app E ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso eX
    let A := ringedSiteOrdinaryHomComparison.{c, v, r, w} J R (E⟦(1 : ℤ)⟧) I ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (((shiftFunctor _ (1 : ℤ)).map eX.inv) ≫
          (Q.commShiftIso (1 : ℤ)).inv.app E).op eM.hom)
    letI : IsIso A := by
      convert representativeComparison_isIso.{c, v, r, w} J R I M (X⟦(1 : ℤ)⟧)
        (E⟦(1 : ℤ)⟧) eM eXS using 1
      rfl
    have hn := sourceShift_raw.{c, v, r, w} J R X M E I eX eM (1 : ℤ)
    have hc := dualComparison_shift.{c, v, r, w} J R I M eM S hS X E eX (-1 : ℤ)
    rw [triangulatedOrdinaryCommShift_neg_one.{c, v, r}] at hc
    simp only [Int.reduceNeg] at hn hc
    have hn' := (Category.assoc _ _ _).trans hn
    have hc' := hc.trans (Category.assoc _ _ _).symm
    have hr := (Q.mapIso ((rawSourceIso.{c, v, r} J R I (1 : ℤ)).app (op E))).hom_inv_id
    dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hr
    apply positive_normalization_of_comparisons hn' hc' hr
    exact (T.commShiftIso (-1 : ℤ)).hom_inv_id_app (op X)

private theorem dualExactOfCone (I : Complex.{c, v, r} J R) [I.IsKInjective]
    (M : D.{c, v, r, w} J R) (eM : DerivedCategory.Q.obj I ≅ M)
    (S : (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).CommShift ℤ)
    (hS : letI := S; NatTrans.CommShift (dualComparison.{c, v, r, w} J R I M eM).hom ℤ)
    (hcone : ∀ {E G : Complex.{c, v, r} J R} (f : E ⟶ G),
      Nonempty (CochainComplex.mappingCocone.triangle ((ordinaryDual.{c, v, r} J R I).map f.op) ≅
        (triangulatedOrdinaryDual.{c, v, r} J R I).mapTriangle.obj
        (oppositeConeTriangle.{c, v, r} J R f))) :
    letI := S
    (Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R).IsTriangulated := by
  letI := S
  letI := hS
  let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
  let F := triangulatedOrdinaryDual.{c, v, r} J R I
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let e := dualComparison.{c, v, r, w} J R I M eM
  constructor
  intro Δ hΔ
  obtain ⟨Δ', hΔ', ⟨e₁⟩⟩ :=
    (Pretriangulated.Opposite.mem_distinguishedTriangles_iff' Δ).mp hΔ
  obtain ⟨E, G, f, ⟨e₂⟩⟩ := (DerivedCategory.mem_distTriang_iff Δ').mp hΔ'
  let K := oppositeConeTriangle.{c, v, r} J R f
  let eΔ : Δ ≅ Q.op.mapTriangle.obj K :=
    e₁ ≪≫ (Pretriangulated.triangleOpEquivalence (D.{c, v, r, w} J R)).functor.mapIso
      e₂.symm.op ≪≫ Q.mapTriangleOpCompTriangleOpEquivalenceFunctorApp _
  have h₁ : IsIso (e.hom.app K.obj₁) := inferInstance
  have h₂ : IsIso (e.hom.app K.obj₂) := inferInstance
  have h₃ : IsIso (e.hom.app K.obj₃) := inferInstance
  let eτ := triangleComparisonAux (F ⋙ Q) (Q.op ⋙ T) e.hom K
  obtain ⟨ec⟩ := hcone f
  let et : Q.mapTriangle.obj
      (CochainComplex.mappingCocone.triangle ((ordinaryDual.{c, v, r} J R I).map f.op)) ≅
      T.mapTriangle.obj Δ :=
    Q.mapTriangle.mapIso ec ≪≫ (Functor.mapTriangleCompIso F Q).symm.app K ≪≫ eτ ≪≫
      (Functor.mapTriangleCompIso Q.op T).app K ≪≫ T.mapTriangle.mapIso eΔ.symm
  exact Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.mappingCocone_triangle_distinguished ((ordinaryDual.{c, v, r} J R I).map f.op))
    _ et.symm

end CategoryTheory.RingedHomUniverses

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- Contravariant derived Hom is exact with the coherently normalized signed source shift.
Source: Stacks 08JC (lemma-RHom-triangulated) and 0A8X (Hom-complex differential).
(blueprint: lem-coef-signed-derived-internal-hom-exact).
Proof: Represent M by a K-injective I. The signed source comparison on Hom complexes
multiplies the reindexed degree-q family for E[m] by (-1)^(m*q). For the opposite-category
shift n this uses m=-n. Raw comparisons have the addition discrepancy (-1)^(n*m).
Multiply the degree-n comparison by (-1)^(n*(n+1)/2). The identity
q(n+m)=q(n)+q(m)+n*m cancels that discrepancy and gives zero and addition coherence for
all integers. At n=1 this correction is -1; at n=-1 it is 1. The fixed ordinary-to-derived
augmentation and its uniqueness therefore give exactly the two displayed normalizations.
For a cone of E -> G, ordinary Hom into I is the graded direct sum of Hom(G,I) and
Hom(E,I)[-1]. Its differential is (d*x,d*y+(-1)^(q+1)*f*(x)). The degree-q map
(x,y) -> (x,(-1)^(q+1)*y), in cone-summand order, identifies it with Cone(f*)[-1].
Rotation and the specified opposite triangle sign identify all three arrows. For the connecting
arrow, the minus in the degree-one comparison turns the reversed third arrow into cone inclusion.
Hom into I inverts quasi-isomorphisms, so localize these identities.
Every distinguished derived triangle is isomorphic to a localized cone triangle; transport
along this isomorphism proves exactness. No double dual or bidual evaluation map is used. -/
theorem signedDerivedInternalHom_exact (M : D.{c, v, r, w} J R) :
    let T := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R
    ∃ S : T.CommShift ℤ,
      (fun [_shiftInst : T.CommShift ℤ] ↦ T.IsTriangulated ∧
        (∀ X : D.{c, v, r, w} J R,
          (T.commShiftIso (1 : ℤ)).hom.app (op X) =
            -(sourceShift.{c, v, r, w} J R X (-1)).inv.app M) ∧
        (∀ X : D.{c, v, r, w} J R,
          (T.commShiftIso (-1 : ℤ)).inv.app (op X) =
            (sourceShift.{c, v, r, w} J R X 1).hom.app M)) (_shiftInst := S) := by
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let ι : CochainComplex.KInjectives (Modules.{c, v, r} J R) ⥤
      Complex.{c, v, r} J R := CochainComplex.KInjectives.ι
  letI : Abelian.HasKInjectiveResolutions (Modules.{c, v, r} J R) :=
    hasKInjectiveResolutions.{c, v, r} J R
  letI : (ι ⋙ Q).EssSurj := kInjectiveQ_essSurj
  let Z := (ι ⋙ Q).objPreimage M
  let I : Complex.{c, v, r} J R := Z.obj
  letI : I.IsKInjective := Z.property
  let eM : DerivedCategory.Q.obj I ≅ M := (ι ⋙ Q).objObjPreimageIso M
  obtain ⟨S, hS⟩ := dualShiftDescent.{c, v, r, w} J R I M eM
  letI := S
  obtain ⟨h₁, h₂⟩ := dualShift_normalized.{c, v, r, w} J R I M eM S hS
  refine ⟨S, ?_, h₁, h₂⟩
  exact dualExactOfCone.{c, v, r, w} J R I M eM S hS
    (fun f ↦ ⟨internalHomConeTriangleIso.{c, v, r} J R I f⟩)

end CategoryTheory
