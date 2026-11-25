/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescent
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy

/-! # Finite Isom sheaves for supplied algebraic adic levels

## References

* Stacks Project, Tags 09BV and 09C6, finite-level isomorphism sheaves
* Stacks Project, Tag 09BV, the construction of I_n and its reduction maps, and Tag 09C6,
  compatibility of finite reductions
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard

private def universal_iso
    {C D : Type*} [Category C] [Category D] {R : C ⥤ D}
    {A A' : D} {K K' : C} {d : A ⟶ R.obj K} {d' : A' ⟶ R.obj K'}
    (h : StructuredArrow.IsUniversal (StructuredArrow.mk d))
    (h' : StructuredArrow.IsUniversal (StructuredArrow.mk d')) (e : A ≅ A') : K ≅ K' where
  hom := h.desc (StructuredArrow.mk (e.hom ≫ d'))
  inv := h'.desc (StructuredArrow.mk (e.inv ≫ d))
  hom_inv_id := by
    apply h.hom_ext
    rw [Functor.map_comp, ← Category.assoc, h.fac]
    change (e.hom ≫ d') ≫ R.map (h'.desc (StructuredArrow.mk (e.inv ≫ d))) =
      d ≫ R.map (𝟙 K)
    rw [Category.assoc]
    have hf : d' ≫ R.map (h'.desc (StructuredArrow.mk (e.inv ≫ d))) = e.inv ≫ d := h'.fac _
    rw [hf]
    change e.hom ≫ e.inv ≫ d = d ≫ R.map (𝟙 K)
    rw [← Category.assoc, e.hom_inv_id]
    simp
  inv_hom_id := by
    apply h'.hom_ext
    rw [Functor.map_comp, ← Category.assoc, h'.fac]
    change (e.inv ≫ d) ≫ R.map (h.desc (StructuredArrow.mk (e.hom ≫ d'))) =
      d' ≫ R.map (𝟙 K')
    rw [Category.assoc]
    have hf : d ≫ R.map (h.desc (StructuredArrow.mk (e.hom ≫ d'))) = e.hom ≫ d' := h.fac _
    rw [hf]
    change e.inv ≫ e.hom ≫ d' = d' ≫ R.map (𝟙 K')
    rw [← Category.assoc, e.inv_hom_id]
    simp

private theorem universal_of_bijective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X : D} {Y : C} (t : X ⟶ F.obj Y)
    (h : ∀ Z : C, Function.Bijective (fun k : Y ⟶ Z ↦ t ≫ F.map k)) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk t)) := by
  classical
  let lift (Z : StructuredArrow X F) : StructuredArrow.mk t ⟶ Z :=
    StructuredArrow.homMk ((h Z.right).2 Z.hom).choose ((h Z.right).2 Z.hom).choose_spec
  refine ⟨IsInitial.ofUniqueHom lift ?_⟩
  intro Z a
  apply StructuredArrow.hom_ext
  apply (h Z.right).1
  exact a.w.trans ((h Z.right).2 Z.hom).choose_spec.symm

private theorem conjugate_square
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    (H : C' ⥤ C) (F : C ⥤ D) (G : C' ⥤ D) (α : H ⋙ F ≅ G)
    {P Q : C} {P' Q' : C'} (dP : P ⟶ H.obj P') (dQ : Q ⟶ H.obj Q')
    {A A' B B' : D} (a : A ⟶ A') (b : B ⟶ B')
    (actual : F.obj Q ≅ A) (actual' : G.obj Q' ≅ A')
    (model : F.obj P ≅ B) (model' : G.obj P' ≅ B')
    (ha : F.map dQ ≫ α.hom.app Q' ≫ actual'.hom = actual.hom ≫ a)
    (hb : F.map dP ≫ α.hom.app P' ≫ model'.hom = model.hom ≫ b)
    (e : P ≅ Q) (e' : P' ≅ Q')
    (he : e.hom ≫ dQ = dP ≫ H.map e'.hom) :
    (model.symm ≪≫ F.mapIso e ≪≫ actual).hom ≫ a =
      b ≫ (model'.symm ≪≫ G.mapIso e' ≪≫ actual').hom := by
  symm
  apply (cancel_epi model.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc model.hom b, ← hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← α.hom.naturality_assoc e'.hom]
  change F.map dP ≫ F.map (H.map e'.hom) ≫ α.hom.app Q' ≫ actual'.hom = _
  rw [← F.map_comp_assoc, ← he, F.map_comp, Category.assoc, ha]

/-- The finite Isom sheaves, their reduction and evaluation on contractible objects.
This constructs neither a covering nor a compatible family of markings. -/
theorem lisse_tower_isomorphism_sections
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1}
      (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right
          (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A)))
          (Nat.le_succ (n + 1))))).mapDerivedCategory.obj
          (K n))
    (huniversal : ∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{u + 1}
        (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))),
      Function.Bijective (fun k : K n ⟶ N ↦ t n ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right
            (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A)))
            (Nat.le_succ (n + 1))))).mapDerivedCategory.map
            k))
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (K n)))
    (hfinite : ∀ (n : ℕ) (q : ℤ), Module.Finite
      (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) q).obj (K n)))
    (hmodels : ∀ n : ℕ, ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj (K n) ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj (M.level n))) :
    let C := AdicCompletion d.ideal A
    let J := d.ideal.map (algebraMap A C)
    let R (n : ℕ) := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (Ideal.Quotient.mk (J ^ (n + 1)))
    let s (n : ℕ) := (R (n + 1)).mapDerivedCategory.map (t n) ≫
      (Functor.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))
        (R (n + 1))).symm.inv.app (K n) ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
        (Ideal.Quotient.mk (J ^ (n + 2)))
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (J ^ (n + 1)))
        (Ideal.Quotient.factor_comp_mk _).symm)).inv.app (K n)
    ∃ (I : ℕ → Sheaf U.left.smallEtaleTopology (Type (u + 1)))
      (r : ∀ n : ℕ, I (n + 1) ⟶ I n)
      (ev : ∀ (V : U.left.ProEt), IsAffine V.left →
        (ProEt.topology U.left).IsWeaklyContractible.{u + 1} V →
        ∀ (W : Y.ProEt), (W ⟶ ProEt.mk (V.hom ≫ U.hom)) → ∀ n : ℕ,
        ((Functor.sheafPullbackConstruction.sheafPullback (toProEt U.left)
          (Type (u + 1)) U.left.smallEtaleTopology (ProEt.topology U.left)).obj
            (I n)).obj.obj (op V) →
        ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj (K n) ≅
          (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj
            (M.level n))),
      (∀ n : ℕ, IsLisseEtaleSheafOfSets (I n)) ∧
      (∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ U.left), Nonempty ((pointSmallEtale x).sheafFiber.obj (I n))) ∧
      ∀ (V : U.left.ProEt) (ha : IsAffine V.left)
        (hw : (ProEt.topology U.left).IsWeaklyContractible.{u + 1} V)
        (W : Y.ProEt) (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
        (v : ((Functor.sheafPullbackConstruction.sheafPullback (toProEt U.left)
          (Type (u + 1)) U.left.smallEtaleTopology (ProEt.topology U.left)).obj
            (I (n + 1))).obj.obj (op V)),
        let v' := ((Functor.sheafPullbackConstruction.sheafPullback (toProEt U.left)
          (Type (u + 1)) U.left.smallEtaleTopology (ProEt.topology U.left)).map
            (r n)).hom.app (op V) v
        let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
        let znext := (constantAdicQuotientRightIso (W.hom ≫ g) d (n + 1)).hom.app
          (K (n + 1)) ≫ (H (n + 1)).map (ev V ha hw W f (n + 1) v).hom
        let zprev := (constantAdicQuotientRightIso (W.hom ≫ g) d n).hom.app (K n) ≫
          (H n).map (ev V ha hw W f n v').hom
        znext ≫ (H (n + 1)).map
            (adicTowerRestrictedTransition d (W.hom ≫ g) M (n + 1) n (Nat.le_succ n)) ≫
          (pbcDerivedRestrictComp
            (constantAdicFiniteProjection (W.hom ≫ g) d (n + 1))
            ((adicTowerInverseImage (W.hom ≫ g)).map
              (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
            (constantAdicFiniteProjection (W.hom ≫ g) d n)
            (constantAdicFiniteProjection_comp (W.hom ≫ g) d (n + 1) n
              (Nat.le_succ n))).hom.app
                ((adicTowerPullback (W.hom ≫ g)
                  ((pbcAdicRings X d).obj (op n))).obj (M.level n)) =
          (constantAdicFiniteRealization (W.hom ≫ g) d).map (s n) ≫ zprev := by
  classical
  obtain ⟨D⟩ := lisse_tower_etale_descent X Y g d M U K hbounded hfinite hmodels
  have (n : ℕ) : Finite (lisseTowerEtaleRing d n) := by
    have : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
    exact Finite.of_surjective (constantAdicQuotientMap d.ideal n)
      (quotient_map_bijective d.ideal d.finitelyGenerated n).2
  let C (n : ℕ) := (normalizationConstant U.left.smallEtaleTopology).obj (K n)
  have hCbounded (n : ℕ) : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (C n)) := by
    obtain ⟨a, b, hab⟩ := hbounded n
    exact ⟨a, b, fun q hq ↦
      Functor.isZero_homologyFunctor_mapDerivedCategory_obj
        (constantSheaf U.left.smallEtaleTopology
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) (hab q hq)⟩
  have hClisse (n : ℕ) (q : ℤ) : IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj (C n)) := by
    have := hfinite n q
    have : IsFiniteLocallyConstantSheaf
        ((constantSheaf U.left.smallEtaleTopology
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))).obj
            ((DerivedCategory.homologyFunctor _ q).obj (K n))) :=
      AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_constantSheaf (X := U.left) _
    have ec :
        (constantSheaf U.left.smallEtaleTopology
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))).obj
            ((DerivedCategory.homologyFunctor _ q).obj (K n)) ≅
        (DerivedCategory.homologyFunctor _ q).obj (C n) := by
      simpa only [Functor.comp_obj, C, normalizationConstant] using
        (((constantSheaf U.left.smallEtaleTopology
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))).mapDerivedCategoryHomologyFunctorIso
            q).app (K n))
    exact IsFiniteLocallyConstantSheaf.of_iso ec
  have hη (n : ℕ) : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (t n))) :=
    universal_of_bijective (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
      (t n) (huniversal n)
  let red (n : ℕ) (V : U.left.Etale)
      (e : (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) V).obj
          (C (n + 1)) ≅
        (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) V).obj
          (D.D (n + 1))) :=
    universal_iso (D.local_constant_universal n (K (n + 1)) (K n) (t n) (hη n) V).some
      (D.local_delta_universal n V).some e
  have hred (n : ℕ) (V : U.left.Etale)
      (e : (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) V).obj
          (C (n + 1)) ≅
        (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) V).obj
          (D.D (n + 1))) :
      e.hom ≫ etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
          (D.delta n) V =
        etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
          (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
            (t n)) V ≫ (normalizationRestrict V.left.smallEtaleTopology
              (lisseTowerEtaleQuotient d n)).map (red n V e).hom :=
    by
      simpa only [red, universal_iso, StructuredArrow.mk_right,
        StructuredArrow.mk_hom_eq_self] using
        ((D.local_constant_universal n (K (n + 1)) (K n) (t n) (hη n) V).some.fac
          (StructuredArrow.mk (e.hom ≫ etaleIsomorphismNormalizationArrow U.left
            (lisseTowerEtaleQuotient d n) (D.delta n) V))).symm
  let p (n : ℕ) : derivedLocalIsomorphismPresheaf (C (n + 1)) (D.D (n + 1)) ⟶
      derivedLocalIsomorphismPresheaf (C n) (D.D n) :=
    { app V := TypeCat.ofHom (red n V.unop)
      naturality V Z f := by
        apply ConcreteCategory.hom_ext
        intro e
        change red n Z.unop (localIsomorphismMap (C (n + 1)) (D.D (n + 1)) f.unop e) =
          localIsomorphismMap (C n) (D.D n) f.unop (red n V.unop e)
        apply Iso.ext
        apply (D.local_constant_universal n (K (n + 1)) (K n) (t n) (hη n) Z.unop).some.hom_ext
        exact (hred n Z.unop _).symm.trans
          (D.restriction_square n (K (n + 1)) (K n) (t n) Z.unop V.unop f.unop
            e (red n V.unop e) (hred n V.unop e)) }
  let I (n : ℕ) := derivedLocalIsomorphismSheaf (C n) (D.D n)
  let r (n : ℕ) : I (n + 1) ⟶ I n :=
    (presheafToSheaf U.left.smallEtaleTopology (Type (u + 1))).map (p n)
  let ev (V : U.left.ProEt) (ha : IsAffine V.left)
      (hw : (ProEt.topology U.left).IsWeaklyContractible.{u + 1} V)
      (W : Y.ProEt) (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
      (v : ((comparisonSetUpperStar U.left).obj (I n)).obj.obj (op V)) :=
    (D.model V W f n (K n)).symm ≪≫ (D.realization V W f n).mapIso
      (sourceDerivedIsoEvaluation U.left (lisseTowerEtaleRing d n) (C n) (D.D n)
        V ha hw v) ≪≫ D.actual V W f n
  refine ⟨I, r, ev, ?_, D.stalk, ?_⟩
  · intro n
    exact ((AlgebraicGeometry.Etale.finiteRing_derived_local_constancy U.left
      (lisseTowerEtaleRing d n) (C n) (hCbounded n) (hClisse n)).2.1
        (D.D n) (D.boundedD n) (D.lisseD n)).2
  · intro V ha hw W f n v
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    let F := D.realization V W f (n + 1) ⋙ H (n + 1)
    let G := D.realization V W f n ⋙ H n
    let e := sourceDerivedIsoEvaluation U.left (lisseTowerEtaleRing d (n + 1))
      (C (n + 1)) (D.D (n + 1)) V ha hw v
    let v' := ((comparisonSetUpperStar U.left).map (r n)).hom.app (op V) v
    let e' := sourceDerivedIsoEvaluation U.left (lisseTowerEtaleRing d n)
      (C n) (D.D n) V ha hw v'
    let model (j : ℕ) := (H j).mapIso (D.model V W f j (K j)) ≪≫
      ((constantAdicQuotientRightIso (W.hom ≫ g) d j).app (K j)).symm
    have h := conjugate_square
      (normalizationRestrict (ProEt.topology V.left) (lisseTowerEtaleQuotient d n))
      F G (D.scalar V W f n)
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          (t n)))
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (D.delta n))
      (constantAdicRestrictedStep (W.hom ≫ g) d M n)
      ((constantAdicFiniteRealization (W.hom ≫ g) d).map
        (lisseTowerAlgebraArrow d n (t n)))
      ((H (n + 1)).mapIso (D.actual V W f (n + 1)))
      ((H n).mapIso (D.actual V W f n))
      (model (n + 1)) (model n)
      (D.actual_normalized V W f n) (D.model_normalized V W f n _ _ (t n))
      e e' (sourceIsomorphism_normalized_presheaf_evaluation U.left
        (lisseTowerEtaleQuotient d n) (C (n + 1)) (D.D (n + 1)) (C n) (D.D n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          (t n)) (D.delta n) (p n) (hred n) V ha hw v)
    simpa only [model, F, G, H, e, e', v', ev, lisseTowerAlgebraArrow,
      lisseTowerAlgebraForget, lisseTowerEtaleQuotient, constantAdicRestrictedStep,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
      Iso.app_hom, comparisonSetUpperStar, Nat.add_assoc, Category.assoc] using h

end AlgebraicGeometry.Scheme
