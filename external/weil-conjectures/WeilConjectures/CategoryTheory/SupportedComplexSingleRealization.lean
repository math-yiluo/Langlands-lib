/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

@[expose] public section

universe uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace DerivedCategory.Plus

variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A normalized map from a supported complex is represented by its homology projection.
Source: Stacks Project, derived.tex, Tag 015J, single-complex specialization;
Mathlib's `HomologicalComplex.mkHomToSingle` and pure-degree homology faithfulness.
(blueprint: lem-pc-supported-complex-single-realization)

Proof: All differentials of L vanish, since each has a zero source or target.
Consequently the cycle inclusion and the homology projection in degree n are
isomorphisms. Set φ to the inverse cycle inclusion followed by the homology
projection and the inverse quotient homology comparison. Construct the complex map
with mkHomToSingle φ; the incoming differential equations hold because those
sources are zero. Its degree-n component, followed by the single coefficient
identification, is φ, giving the second equality. Quotient homology naturality and
the single-complex homology comparison show that its derived image induces the
identity on X. Both it and f are maps between pure degree-n objects; faithfulness
of degree-n homology gives the first equality. This also covers n=0 and X=0. -/
theorem supported_complex_single_realization
    (L : CochainComplex.Plus B) (n : ℕ)
    (hL : ∀ i : ℤ, i ≠ (n : ℤ) → IsZero (L.obj.X i)) :
    let X := (homologyFunctor B n).obj (Q.obj L)
    let S : CochainComplex.Plus B :=
      ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
    let e : (DerivedCategory.Plus.singleFunctor B n).obj X ≅
        DerivedCategory.Plus.Q.obj S :=
      DerivedCategory.Plus.ι.preimageIso
        ((DerivedCategory.singleFunctorIsoCompQ B n).app X)
    ∀ (f : Q.obj L ⟶ (singleFunctor B n).obj X),
      (homologyFunctor B n).map f ≫
        (singleFunctorCompHomologyFunctorIso (C := B) n).hom.app X = 𝟙 X →
      ∃ (t : L ⟶ S), Q.map t ≫ e.inv = f ∧
        L.obj.iCycles n ≫ t.hom.f n ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom =
        L.obj.homologyπ n ≫ (homologyFunctorObjQIso L n).inv := by
  dsimp only
  intro f hf
  let X := (homologyFunctor B n).obj (Q.obj L)
  let S : CochainComplex.Plus B :=
    ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
  let e : (singleFunctor B n).obj X ≅ Q.obj S :=
    ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQ B n).app X)
  have hd : L.obj.d (n : ℤ) (n + 1) = 0 :=
    (hL (n + 1) (by omega)).eq_of_tgt _ _
  have : IsIso (L.obj.iCycles n) := L.obj.isIso_iCycles n (n + 1) (by simp) hd
  let φ := inv (L.obj.iCycles n) ≫ L.obj.homologyπ n ≫ (homologyFunctorObjQIso L n).inv
  let t₀ := HomologicalComplex.mkHomToSingle φ (fun i hi ↦
    (hL i (by change i + 1 = (n : ℤ) at hi; omega)).eq_of_src _ _)
  let t : L ⟶ S := ObjectProperty.homMk t₀
  have hc : L.obj.iCycles n ≫ t.hom.f n ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom =
      L.obj.homologyπ n ≫ (homologyFunctorObjQIso L n).inv := by
    dsimp only [t, ObjectProperty.homMk_hom, t₀]
    rw [HomologicalComplex.mkHomToSingle_f]
    simp only [Category.assoc]
    change L.obj.iCycles n ≫ (inv (L.obj.iCycles n) ≫
      L.obj.homologyπ n ≫ (homologyFunctorObjQIso L n).inv) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).inv ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom = _
    simp
  refine ⟨t, ?_, hc⟩
  have hsingle : (singleFunctorCompHomologyFunctorIso (C := B) n).inv.app X ≫
      (homologyFunctorObjQIso S n).hom =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n X).inv := by
    simp only [id_obj, comp_obj, singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorCompHomologyFunctorIso,
      HomologicalComplex.homologyFunctorSingleIso, Iso.trans_inv,
      isoWhiskerLeft_inv, Category.assoc, isoWhiskerRight_inv, mapIso_inv,
      SingleFunctors.evaluation_map, NatTrans.comp_app, NatIso.ofComponents_inv_app,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, Category.id_comp,
      homologyFunctorObjQIso, Iso.app_hom, S]
    rw [DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
    simp
  have he : e.inv = 𝟙 _ := by
    apply ι.map_injective
    simp only [e, Functor.preimageIso_inv, Functor.map_preimage,
      Iso.app_inv, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv,
      NatTrans.id_app]
    rfl
  have hn : (homologyFunctor B n).map (Q.map t ≫ e.inv) ≫
      (singleFunctorCompHomologyFunctorIso (C := B) n).hom.app X = 𝟙 X := by
    rw [he, Category.comp_id]
    apply (cancel_epi (L.obj.homologyπ n ≫ (homologyFunctorObjQIso L n).inv)).1
    simp only [Category.assoc]
    have hsingle' : (homologyFunctorObjQIso S n).inv ≫
        (singleFunctorCompHomologyFunctorIso (C := B) n).hom.app X =
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n X).hom := by
      apply (cancel_mono
        ((singleFunctorCompHomologyFunctorIso (C := B) n).inv.app X)).1
      simp only [Category.assoc, Iso.hom_inv_id_app]
      apply (cancel_mono (homologyFunctorObjQIso S n).hom).1
      simp only [Category.assoc]
      erw [Category.id_comp, Iso.inv_hom_id]
      rw [hsingle]
      simp
    have hnat := homologyFunctorObjQIso_hom_naturality t (n : ℤ)
    have hnat' : (homologyFunctorObjQIso L n).inv ≫
        (homologyFunctor B n).map (Q.map t) =
        HomologicalComplex.homologyMap t.hom n ≫ (homologyFunctorObjQIso S n).inv := by
      apply (cancel_mono (homologyFunctorObjQIso S n).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hnat]
      simp
    rw [reassoc_of% hnat', hsingle', HomologicalComplex.homologyπ_naturality_assoc]
    erw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
      HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
      HomologicalComplex.cyclesMap_i, Category.assoc]
    change L.obj.iCycles n ≫ t.hom.f n ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom = _
    erw [Category.comp_id]
    exact hc
  have hge : L.obj.IsStrictlyGE (n : ℤ) :=
    (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi ↦ hL i (ne_of_lt hi))
  have hle : L.obj.IsStrictlyLE (n : ℤ) :=
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hL i (ne_of_gt hi))
  have : (Q.obj L).IsGE (n : ℤ) := by
    apply (isGE_ι_obj_iff _ _).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsGE (n : ℤ))
  have : (Q.obj L).IsLE (n : ℤ) := by
    apply (isLE_ι_obj_iff _ _).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsLE (n : ℤ))
  apply singleFunctor_hom_ext_of_isGE_of_isLE (n : ℤ)
  apply (cancel_mono ((singleFunctorCompHomologyFunctorIso (C := B) n).hom.app X)).1
  exact hn.trans hf.symm

end DerivedCategory.Plus
