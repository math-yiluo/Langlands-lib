/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
public import WeilConjectures.Algebra.Homology.RingedSiteBoundedDualComponents

/-! # Components of the bounded ordinary sheaf dual

Source: Stacks Project, sites-cohomology.tex, Tags 08JJ and 0A8X
(blueprint: lem-sfb-ringed-site-bounded-dual-components).

The abbreviations below only expand the recorded Hom constructions and the
coefficient sheaf in degree zero. The component is the actual product projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteBoundedDual

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (R : Sheaf J CommRingCat.{max c v r})








attribute [local irreducible] homComplexFunctor homComplexπ

private lemma homMap_zero_right {A B D : Modules.{c, v, r} R} :
    SheafOfModules.homObjMap (R := R) (𝟙 A) (0 : B ⟶ D) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

private lemma homMap_zero_left {A B D : Modules.{c, v, r} R} :
    SheafOfModules.homObjMap (R := R) (0 : A ⟶ B) (𝟙 D) = 0 :=
  SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left (𝟙 _))

private lemma homZero_right (A B : Modules.{c, v, r} R) (hB : IsZero B) :
    IsZero (SheafOfModules.homObj (R := R) A B) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id,
    hB.eq_of_tgt (𝟙 B) 0, homMap_zero_right.{c, v, r}]

private lemma homZero_left (A B : Modules.{c, v, r} R) (hA : IsZero A) :
    IsZero (SheafOfModules.homObj (R := R) A B) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id,
    hA.eq_of_src (𝟙 A) 0, homMap_zero_left.{c, v, r}]

private lemma projection_isIso (E : CochainComplex (Modules.{c, v, r} R) ℤ)
    (p q : ℤ) (h : p + q = 0) :
    IsIso (homComplexπ E (zeroComplex.{c, v, r} R) q p 0 h) := by
  classical
  let Q := fun j : ℤ ↦ SheafOfModules.homObj (R := R)
    (E.X j) ((zeroComplex.{c, v, r} R).X (j + q))
  let hc := homComplexIsLimit E (zeroComplex.{c, v, r} R) q
  let v : Q p ⟶ (complexDual.{c, v, r} R E).X q := Fan.IsLimit.lift hc
    (fun j ↦ if hj : j = p then eqToHom (congrArg Q hj.symm) else 0)
  have hv : v ≫ homComplexπ E (zeroComplex.{c, v, r} R) q p (p + q) rfl = 𝟙 (Q p) := by
    change Fan.IsLimit.lift hc _ ≫
      (Fan.mk _ (fun j : ℤ ↦ homComplexπ E (zeroComplex.{c, v, r} R) q j (j + q) rfl)).proj p = _
    rw [Fan.IsLimit.fac]
    simp
  have hp : homComplexπ E (zeroComplex.{c, v, r} R) q p (p + q) rfl ≫ v = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext hc
    intro j
    change (_ ≫ v) ≫ homComplexπ E (zeroComplex.{c, v, r} R) q j (j + q) rfl =
      𝟙 _ ≫ homComplexπ E (zeroComplex.{c, v, r} R) q j (j + q) rfl
    by_cases hj : j = p
    · subst j
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (homZero_right.{c, v, r} R (E.X j) ((zeroComplex.{c, v, r} R).X (j + q))
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (j + q)
          (by omega))).eq_of_tgt _ _
  have hi := (Iso.mk _ v hp hv).isIso_hom
  have transport {t : ℤ} (ht : p + q = t) :
      IsIso (homComplexπ E (zeroComplex.{c, v, r} R) q p t ht) := by
    subst t
    exact hi
  exact transport h

private def termIso (E : CochainComplex (Modules.{c, v, r} R) ℤ)
    (p q : ℤ) (h : p + q = 0) :
    (complexDual.{c, v, r} R E).X q ≅ dual.{c, v, r} R (E.X p) :=
  letI := projection_isIso.{c, v, r} R E p q h
  asIso (homComplexπ E (zeroComplex.{c, v, r} R) q p 0 h) ≪≫
    ((SheafOfModules.homFunctor R).obj (op (E.X p))).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (coefficient.{c, v, r} R))

private lemma termIso_hom (E : CochainComplex (Modules.{c, v, r} R) ℤ)
    (p q : ℤ) (h : p + q = 0) :
    (termIso.{c, v, r} R E p q h).hom = component.{c, v, r} R E p q h := rfl

private lemma component_d (E : CochainComplex (Modules.{c, v, r} R) ℤ)
    (n m p p' : ℤ) (hnm : n + 1 = m) (h : p + n = 0) (h' : p' + m = 0) :
    (complexDual.{c, v, r} R E).d n m ≫ component.{c, v, r} R E p' m h' =
      m.negOnePow • (component.{c, v, r} R E p n h ≫
        SheafOfModules.homObjMap (E.d p' p) (𝟙 (coefficient.{c, v, r} R))) := by
  unfold component
  rw [← Category.assoc, homComplex_d_π E (zeroComplex.{c, v, r} R)
    n m p' 0 (-1) p hnm h' (by omega) h]
  have hz : (zeroComplex.{c, v, r} R).d (-1) 0 = 0 := rfl
  rw [hz, homMap_zero_right.{c, v, r}, comp_zero, zero_sub]
  simp only [Preadditive.neg_comp, Linear.units_smul_comp,
    Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
    Category.id_comp, Category.comp_id, ← hnm, Int.negOnePow_succ, Units.neg_smul]

private lemma homMap_units_left {A B N : Modules.{c, v, r} R}
    (f : A ⟶ B) (u : ℤˣ) :
    SheafOfModules.homObjMap (R := R) (u • f) (𝟙 N) =
      u • SheafOfModules.homObjMap f (𝟙 N) := by
  let F : (A ⟶ B) →+
      (SheafOfModules.homObj (R := R) B N ⟶ SheafOfModules.homObj (R := R) A N) :=
    { toFun := fun g ↦ SheafOfModules.homObjMap g (𝟙 N)
      map_zero' := homMap_zero_left.{c, v, r} R
      map_add' := fun f g ↦ SheafOfModules.hom_ext
        (PresheafOfModules.homObjMap_add_left f.val g.val (𝟙 _)) }
  exact F.map_zsmul (u : ℤ) f

private def doubleTermIso (E : CochainComplex (Modules.{c, v, r} R) ℤ) (i : ℤ) :
    (complexDual.{c, v, r} R (complexDual.{c, v, r} R E)).X i ≅
      dual.{c, v, r} R (dual.{c, v, r} R (E.X i)) :=
  termIso.{c, v, r} R (complexDual.{c, v, r} R E) (-i) i (neg_add_cancel i) ≪≫
    ((SheafOfModules.homFunctor R).flip.obj (coefficient.{c, v, r} R)).mapIso
      (termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).symm.op

private lemma doubleTermIso_square (E : CochainComplex (Modules.{c, v, r} R) ℤ) (i : ℤ) :
    (doubleTermIso.{c, v, r} R E i).hom ≫
      SheafOfModules.homObjMap (termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).hom
        (𝟙 (coefficient.{c, v, r} R)) =
      component.{c, v, r} R (complexDual.{c, v, r} R E) (-i) i (neg_add_cancel i) := by
  change ((termIso.{c, v, r} R (complexDual.{c, v, r} R E) (-i) i
    (neg_add_cancel i)).hom ≫
    SheafOfModules.homObjMap (termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv
      (𝟙 (coefficient.{c, v, r} R))) ≫ _ = _
  rw [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap, Iso.hom_inv_id,
    Category.id_comp, SheafOfModules.homObjMap_id, Category.comp_id, termIso_hom.{c, v, r}]

private lemma doubleTermIso_d (E : CochainComplex (Modules.{c, v, r} R) ℤ) (i : ℤ) :
    (complexDual.{c, v, r} R (complexDual.{c, v, r} R E)).d i (i + 1) ≫
        (doubleTermIso.{c, v, r} R E (i + 1)).hom =
      -((doubleTermIso.{c, v, r} R E i).hom ≫ SheafOfModules.homObjMap
        (SheafOfModules.homObjMap (E.d i (i + 1)) (𝟙 (coefficient.{c, v, r} R)))
        (𝟙 (coefficient.{c, v, r} R))) := by
  have hd := component_d.{c, v, r} R E (-(i + 1)) (-i) (i + 1) i
    (by omega) (by omega) (add_neg_cancel i)
  rw [Int.negOnePow_neg] at hd
  have hi :
      (termIso.{c, v, r} R E (i + 1) (-(i + 1)) (add_neg_cancel (i + 1))).inv ≫
          (complexDual.{c, v, r} R E).d (-(i + 1)) (-i) =
        i.negOnePow • (SheafOfModules.homObjMap (E.d i (i + 1))
          (𝟙 (coefficient.{c, v, r} R)) ≫
            (termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv) := by
    apply (cancel_mono (termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).hom).mp
    rw [Category.assoc, termIso_hom.{c, v, r}, hd]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, ← termIso_hom.{c, v, r},
      Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (complexDual.{c, v, r} R (complexDual.{c, v, r} R E)).d i (i + 1) ≫
      ((termIso.{c, v, r} R (complexDual.{c, v, r} R E) (-(i + 1)) (i + 1)
        (neg_add_cancel (i + 1))).hom ≫ SheafOfModules.homObjMap
          (termIso.{c, v, r} R E (i + 1) (-(i + 1)) (add_neg_cancel (i + 1))).inv
          (𝟙 (coefficient.{c, v, r} R))) = _
  rw [← Category.assoc, termIso_hom.{c, v, r},
    component_d.{c, v, r} R (complexDual.{c, v, r} R E)
      i (i + 1) (-i) (-(i + 1)) rfl (neg_add_cancel i) (neg_add_cancel (i + 1)),
    Linear.units_smul_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, hi, homMap_units_left.{c, v, r}]
  change (i + 1).negOnePow • (component.{c, v, r} R (complexDual.{c, v, r} R E)
    (-i) i (neg_add_cancel i) ≫
      (i.negOnePow • SheafOfModules.homObjMap _ (𝟙 (coefficient.{c, v, r} R)))) = _
  simp only [Linear.comp_units_smul, smul_smul, Int.negOnePow_succ,
    neg_mul, Int.units_mul_self, Units.neg_smul, one_smul]
  have hc := SheafOfModules.homObjMap_comp_homObjMap (R := R)
    (termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv
    (SheafOfModules.homObjMap (E.d i (i + 1)) (𝟙 (coefficient.{c, v, r} R)))
    (𝟙 (coefficient.{c, v, r} R)) (𝟙 (coefficient.{c, v, r} R))
  simp only [Category.id_comp] at hc
  rw [← hc, ← Category.assoc]
  rfl

/-- The ordinary bounded dual has reversed terms and support, the double-dual
has the negative double-transposed differential, and signed evaluation is a chain map.
The first two equations pin the isomorphisms to the actual product projections.
The last two equations specify ordinary evaluation delta and beta^i = (-1)^i delta.
Thus, for homogeneous phi of degree -i, beta(x)(phi) = (-1)^(i*(-i)) phi(x);
all remaining Hom factors have zero coefficient target.

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, second proof paragraph,
and Section 0A8X (blueprint: lem-sfb-ringed-site-bounded-dual-components).

Proof:
1. By def-pur-hom-complex and def-pur-sheaf-hom, project the degree-q
   Hom product to p=-q. Insert a local map into this factor and zero into all
   other factors, whose coefficient targets vanish. These operations are linear,
   restriction compatible and inverse, giving alpha.
2. Outside [-b,-a], E^(-q) is zero by the bound. Its sheaf dual is zero,
   so alpha gives the claimed support, also when a>b.
3. The coefficient complex has zero differential. The Hom differential of
   def-pur-hom-complex therefore becomes (-1)^(q+1) precomposition by d_E.
4. Repeat the projection for D, and dualize alpha in degree -i, to obtain gamma.
   The two consecutive Hom signs multiply to -1. Linearity then gives the
   negative double transpose of d_E, with no exactness assumption.
5. By def-pur-sheaf-hom, evaluate every local functional on the restriction
   of x to each slice object. This is linear in both arguments and commutes
   with restriction, hence defines delta. The homogeneous Koszul sign is
   (-1)^(i*(-i)) = (-1)^i, since i*i and i have the same parity.
6. Define beta degreewise using gamma inverse and (-1)^i delta. Evaluate the
   chain-map equation on every slice functional: the negative bidual differential
   changes (-1)^i to (-1)^(i+1), while naturality of evaluation moves d_E to x.
   Extensionality gives the chain-map equation. No finite-free retract,
   reflexivity, or exactness of the terms was used. -/
theorem boundedDualComponents
    (E : CochainComplex (Modules.{c, v, r} R) ℤ) (a b : ℤ)
    (hE : ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) :
    ∃ (α : ∀ (p q : ℤ), p + q = 0 →
        ((complexDual.{c, v, r} R E).X q ≅ dual.{c, v, r} R (E.X p)))
      (γ : ∀ i : ℤ, (complexDual.{c, v, r} R (complexDual.{c, v, r} R E)).X i ≅
        dual.{c, v, r} R (dual.{c, v, r} R (E.X i)))
      (δ : ∀ i : ℤ, E.X i ⟶ dual.{c, v, r} R (dual.{c, v, r} R (E.X i)))
      (β : E ⟶ complexDual.{c, v, r} R (complexDual.{c, v, r} R E)),
      (∀ (p q : ℤ) (h : p + q = 0), (α p q h).hom = component.{c, v, r} R E p q h) ∧
      (∀ i : ℤ, (γ i).hom ≫
          SheafOfModules.homObjMap (α i (-i) (add_neg_cancel i)).hom
            (𝟙 (coefficient.{c, v, r} R)) =
        component.{c, v, r} R (complexDual.{c, v, r} R E) (-i) i (neg_add_cancel i)) ∧
      (∀ q : ℤ, (complexDual.{c, v, r} R E).d q (q + 1) ≫
          (α (-(q + 1)) (q + 1) (neg_add_cancel (q + 1))).hom =
        (q + 1).negOnePow • ((α (-q) q (neg_add_cancel q)).hom ≫
          SheafOfModules.homObjMap (E.d (-(q + 1)) (-q)) (𝟙 (coefficient.{c, v, r} R)))) ∧
      (∀ i : ℤ,
        (complexDual.{c, v, r} R (complexDual.{c, v, r} R E)).d i (i + 1) ≫ (γ (i + 1)).hom =
        -((γ i).hom ≫ SheafOfModules.homObjMap
          (SheafOfModules.homObjMap (E.d i (i + 1)) (𝟙 (coefficient.{c, v, r} R)))
          (𝟙 (coefficient.{c, v, r} R)))) ∧
      (∀ q : ℤ, q < -b ∨ -a < q → IsZero ((complexDual.{c, v, r} R E).X q)) ∧
      (∀ (i : ℤ) (U : Cᵒᵖ) (x : (E.X i).val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : (dual.{c, v, r} R (E.X i)).val.obj (op W.unop.left)),
        ((((δ i).val.app U).hom x).app W).hom φ =
          (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            ((E.X i).val.map W.unop.hom.op x)) ∧
      (∀ (i q t : ℤ) (h : i + q = t) (h' : q + i = t)
        (U : Cᵒᵖ) (x : (E.X i).val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : ((complexDual.{c, v, r} R E).X q).val.obj (op W.unop.left)),
        ((((homComplexπ (complexDual.{c, v, r} R E) (zeroComplex.{c, v, r} R)
          i q t h').val.app U).hom (((β.f i).val.app U).hom x)).app W).hom φ =
        (i * q).negOnePow •
          ((((homComplexπ E (zeroComplex.{c, v, r} R) q i t h).val.app
            (op W.unop.left)).hom φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
              ((E.X i).val.map W.unop.hom.op x)) ∧
      (∀ i : ℤ, β.f i ≫ (γ i).hom = i.negOnePow • δ i) := by
  classical
  let : EssentiallySmall.{max c v r} C := essentiallySmallSelf.{r} C
  let := (SheafOfModules.coefficientSheafification.{c, v, max c v r} J).1
  let := (SheafOfModules.coefficientSheafification.{c, v, max c v r} J).2
  let := HasDerivedCategory.standard (Modules.{c, v, r} R)
  obtain ⟨β, hβ, _⟩ := ringedSiteOrdinaryBidual_existsUnique.{c, v, r, (max c v r) + 1} J R E
  change E ⟶ complexDual.{c, v, r} R (complexDual.{c, v, r} R E) at β
  let δ : ∀ i : ℤ, E.X i ⟶ dual.{c, v, r} R (dual.{c, v, r} R (E.X i)) :=
    fun i ↦ i.negOnePow • (β.f i ≫ (doubleTermIso.{c, v, r} R E i).hom)
  refine ⟨termIso.{c, v, r} R E, doubleTermIso.{c, v, r} R E, δ, β, termIso_hom.{c, v, r} R E,
    doubleTermIso_square.{c, v, r} R E, ?_, doubleTermIso_d.{c, v, r} R E, ?_, ?_, ?_, ?_⟩
  · intro q
    simpa only [termIso_hom.{c, v, r}] using component_d.{c, v, r} R E q (q + 1) (-q) (-(q + 1))
      rfl (neg_add_cancel q) (neg_add_cancel (q + 1))
  · intro q hq
    exact (homZero_left.{c, v, r} R (E.X (-q)) (coefficient.{c, v, r} R)
      (hE (-q) (by omega))).of_iso (termIso.{c, v, r} R E (-q) q (neg_add_cancel q))
  · intro i U x W φ
    let e : (E.X i ⟶ dual.{c, v, r} R (dual.{c, v, r} R (E.X i))) →+
        (coefficient.{c, v, r} R).val.obj (op W.unop.left) :=
      { toFun := fun f ↦ ((((f.val.app U).hom x).app W).hom φ)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    have he := e.map_zsmul (i.negOnePow : ℤ) (β.f i ≫ (doubleTermIso.{c, v, r} R E i).hom)
    change e (δ i) = _
    rw [show e (δ i) = i.negOnePow • e (β.f i ≫ (doubleTermIso.{c, v, r} R E i).hom) from he]
    dsimp only [e]
    change i.negOnePow •
      (((((homComplexπ (complexDual.{c, v, r} R E) (zeroComplex.{c, v, r} R) i (-i) 0
        (neg_add_cancel i)).val.app U).hom (((β.f i).val.app U).hom x)).app W).hom
          (((termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv.val.app
            (op W.unop.left)).hom φ)) = _
    have hb := hβ i (-i) (add_neg_cancel i) (neg_add_cancel i) U x W
      (((termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv.val.app
        (op W.unop.left)).hom φ)
    change
      (((((homComplexπ (complexDual.{c, v, r} R E) (zeroComplex.{c, v, r} R) i (-i) 0
        (neg_add_cancel i)).val.app U).hom (((β.f i).val.app U).hom x)).app W).hom
          (((termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv.val.app
            (op W.unop.left)).hom φ)) =
        (i * -i).negOnePow •
          (((((homComplexπ E (zeroComplex.{c, v, r} R) (-i) i 0
            (add_neg_cancel i)).val.app (op W.unop.left)).hom
              (((termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv.val.app
                (op W.unop.left)).hom φ)).app (op (Over.mk (𝟙 W.unop.left)))).hom
                  ((E.X i).val.map W.unop.hom.op x)) at hb
    rw [hb]
    simp only [mul_neg, Int.negOnePow_neg, Int.negOnePow_mul_self,
      smul_smul, Int.units_mul_self, one_smul]
    have hinv := congrArg
      (fun f : dual.{c, v, r} R (E.X i) ⟶ dual.{c, v, r} R (E.X i) ↦
        ((f.val.app (op W.unop.left)).hom φ))
      (termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv_hom_id
    change ((homComplexπ E (zeroComplex.{c, v, r} R) (-i) i 0 (add_neg_cancel i)).val.app
      (op W.unop.left)).hom
        (((termIso.{c, v, r} R E i (-i) (add_neg_cancel i)).inv.val.app
          (op W.unop.left)).hom φ) = φ at hinv
    rw [hinv]
    rfl
  · intro i q t h h' U x W φ
    by_cases ht : t = 0
    · rcases ht with rfl
      exact hβ i q (by omega) (by omega) U x W φ
    · have hz : IsZero ((zeroComplex.{c, v, r} R).X t) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (coefficient.{c, v, r} R) t ht
      have hz' (y : ((zeroComplex.{c, v, r} R).X t).val.obj (op W.unop.left)) :
          y = 0 :=
        congrArg (fun f : (zeroComplex.{c, v, r} R).X t ⟶
            (zeroComplex.{c, v, r} R).X t ↦
          ((f.val.app (op W.unop.left)).hom y)) (hz.eq_of_src (𝟙 _) 0)
      exact (hz' _).trans (hz' _).symm
  · intro i
    dsimp only [δ]
    rw [smul_smul, Int.units_mul_self, one_smul]

end CategoryTheory.RingedSiteBoundedDual
