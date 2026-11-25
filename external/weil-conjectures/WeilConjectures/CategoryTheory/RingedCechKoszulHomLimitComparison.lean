/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic

/-! # Internal Hom of Cech and a prescribed strict derived limit

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local instance 20000] ringedCompletionHasSheafCompose
attribute [local irreducible] ringedHomUnitEvaluationIso

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

private instance ringedModuleGrothendieck : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.isGrothendieckAbelian _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Keep the canonical localization factorization behind its typed interface. -/
private def ringedHomCanonicalFactorization :
    (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙ derivedInternalHom J O ≅
      (𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{u}
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ DerivedCategory.Q := by
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let η := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  exact Localization.fac
    ((𝟭 _).prod I ⋙
      Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts J O I η
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Unfold the completion unit once, keeping the localization factorization bounded. -/
private theorem ringedDerivedHomUnit_factorization (E : ringedSiteDerived O) :
    ringedDerivedHomUnit O E =
      (DerivedCategory.Q.objObjPreimageIso E).inv ≫
        DerivedCategory.Q.map
          ((CochainComplex.toKInjectiveResolution.{u} (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).app
              (DerivedCategory.Q.objPreimage E)) ≫
        (DerivedCategory.Q.mapIso (ringedHomUnitEvaluationIso O
          ((CochainComplex.kInjectiveResolutionFunctor.{u} (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).obj
              (DerivedCategory.Q.objPreimage E)))).inv ≫
        ((ringedHomCanonicalFactorization O).app
          (op (ringedSiteRingComplex O), DerivedCategory.Q.objPreimage E)).inv ≫
        (derivedInternalHom J O).map
          (X := (op (DerivedCategory.Q.obj (ringedSiteRingComplex O)),
            DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)))
          (Y := (op (DerivedCategory.Q.obj (ringedSiteRingComplex O)), E))
          (𝟙 _, (DerivedCategory.Q.objObjPreimageIso E).hom) := by
  rfl

variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

attribute [local irreducible] ringedHomCanonicalFactorization

attribute [local irreducible] ringedExtendedCech ringedKoszulTensorTowerComplex
  ringedKoszulLimitUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The product-localization factorization requires several large functor type comparisons.
/-- The telescope/Hom calculation identifies Cech internal Hom with any specified
presentation of the actual strict Koszul tensor tower and its derived inverse limit.

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941;
more-algebra.tex, Tag 0913; derived.tex, Tag 0949.
(auxiliary; not a blueprint node).

Proof: compose the augmentation-compatible colimit identification with the canonical
telescope-to-colimit quasi-isomorphism. Apply Hom into a functorial K-injective I.
Hom of each finite positive Koszul complex identifies, by finite evaluation with its
usual total-complex sign, with I tensor its dual. Hom of the telescope is the fibre
of 1-shift on the product of these complexes. Finite split-perfect tensor preserves
K-injectivity, so these products compute derived products. The strict-tower Roos
calculation identifies that fibre with the derived inverse limit of the actual tensor
tower. Its canonical comparison with D.inverseLimit is fixed by the right-derived
universal property and its comparison on K-injective towers; D.tensorFactors fixes
the descent of the actual tensor tower. These identifications are natural before
localization, hence descend to the displayed natural isomorphism. The augmentation
sends x to the fibre coordinate (0,(x)_m), which is the image of the actual degree-zero
Koszul tensor units in the strict derived limit. This proves the unit equation on
complexes, and the representative isomorphisms in D.unit prove it on every derived
object. No restriction comparison or uniqueness of completion-normalized maps is
used. The empty list and zero or invertible generators obey the same calculation. -/
theorem exists_ringed_cech_koszul_hom_limit_comparison
    (D : RingedKoszulLimitPresentation O r b) :
    ∃ theta : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅ D.completion,
      ∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
        (ringedExtendedCech O r b).2 E ≫ theta.hom.app E = D.unit E := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q := DerivedCategory.Q (C := A)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let K := (ringedExtendedCech O r b).1
  let ε := (ringedExtendedCech O r b).2
  let T := ringedKoszulTensorTowerFunctor O r b
  let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)
  let F := ringedCechCompletionFunctor O K
  let H := homComplexFunctor (R := O)
  obtain ⟨α, hα⟩ := exists_ringed_cech_koszul_colimit_iso O r b
  obtain ⟨e, he⟩ := exists_ringedKoszul_colimitHom_ordinaryLimit_iso O r b
  let v : H.obj (op K) ≅ T ⋙ L := H.mapIso α.op ≪≫ e
  let a : H.obj (op (ringedSiteRingComplex O)) ≅ 𝟭 _ :=
    NatIso.ofComponents (ringedHomUnitEvaluationIso O) (by
      intro M N f
      exact ringedHomUnitEvaluationIso_naturality O f)
  let z : 𝟭 (ringedSiteComplex O) ⟶ T ⋙ L :=
    a.inv ≫ H.map ε.op ≫ v.hom
  have hz (N : ringedSiteComplex O) : z.app N = ringedKoszulLimitUnit O r b N := by
    change (ringedHomUnitEvaluationIso O N).inv ≫ (H.map ε.op).app N ≫
      (H.map α.hom.op).app N ≫ e.hom.app N = _
    rw [← NatTrans.comp_app_assoc, ← H.map_comp, ← op_comp, hα]
    exact he N
  let d : T ⋙ L ⋙ Q ⟶ T ⋙ DerivedCategory.Q ⋙ D.inverseLimit :=
    Functor.whiskerLeft T D.comparison
  let f : T ⋙ DerivedCategory.Q ⋙ D.inverseLimit ≅ Q ⋙ D.completion :=
    (Functor.isoWhiskerRight D.tensorFactors D.inverseLimit).symm
  let c : (Q.op.prod Q) ⋙ derivedInternalHom J O ≅
      (𝟭 _).prod I ⋙ Functor.uncurry.obj H ⋙ Q := ringedHomCanonicalFactorization O
  let cK : Q ⋙ F ≅ I ⋙ H.obj (op K) ⋙ Q :=
    NatIso.ofComponents (fun M ↦ c.app (op K, M)) (by
      intro M N g
      have hc := c.hom.naturality (X := (op K, M)) (Y := (op K, N)) (𝟙 _, g)
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
        Functor.id_obj, Functor.id_map, Functor.op_obj, Functor.op_map,
        Functor.uncurry_obj_map] at hc
      simpa only [unop_id, Functor.map_id, op_id, NatTrans.id_app, Category.id_comp,
        F, ringedCechCompletionFunctor, Functor.comp_map, Functor.curry_obj_obj_map,
        Functor.comp_obj, Functor.prod_obj, Functor.op_obj,
        Functor.curry_obj_obj_obj, Functor.id_obj, Iso.app_hom, Q]
        using hc)
  have hd (M : ringedSiteComplex O) : IsIso ((Functor.whiskerLeft I d).app M) := by
    have : (I.obj M).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M
    exact ringedKoszulTensorTower_limit_comparison_isIso O r b D (I.obj M)
  have : IsIso (Functor.whiskerLeft I d) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hd
  have hη (M : ringedSiteComplex O) : IsIso (Q.map (η.app M)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
  have : IsIso (Functor.whiskerRight η Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hη
  let qη : Q ≅ I ⋙ Q := asIso (Functor.whiskerRight η Q)
  let t : Q ⋙ F ≅ Q ⋙ D.completion :=
    cK ≪≫ Functor.isoWhiskerLeft I (Functor.isoWhiskerRight v Q) ≪≫
      asIso (Functor.whiskerLeft I d) ≪≫ Functor.isoWhiskerLeft I f ≪≫
      (Functor.isoWhiskerRight qη D.completion).symm
  let full := Localization.fullyFaithfulWhiskeringLeft Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (ringedSiteDerived O)
  let θ : F ≅ D.completion := full.preimageIso t
  have hθ (M : ringedSiteComplex O) : θ.hom.app (Q.obj M) = t.hom.app M :=
    congrArg (fun k ↦ k.app M) (full.map_preimage t.hom)
  have hu (M N : ringedSiteComplex O) (g : M ⟶ N) :
      Q.map g ≫ D.unitOnComplex N = D.unitOnComplex M ≫ D.completion.map (Q.map g) := by
    have hn := z.naturality g
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [hz M, hz N] at hn
    have hc := d.naturality g
    have hf := f.hom.naturality g
    dsimp only [Functor.comp_map] at hc hf
    change Q.map g ≫ (Q.map (ringedKoszulLimitUnit O r b N) ≫
        d.app N ≫ f.hom.app N) =
      (Q.map (ringedKoszulLimitUnit O r b M) ≫ d.app M ≫ f.hom.app M) ≫
        D.completion.map (Q.map g)
    rw [← Category.assoc, ← Q.map_comp, hn, Q.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hc, hf]
  refine ⟨θ, ?_⟩
  intro E
  let M := Q.objPreimage E
  let eM := Q.objObjPreimageIso E
  have hcε := c.inv.naturality (X := (op (ringedSiteRingComplex O), M))
    (Y := (op K, M)) (ε.op, 𝟙 M)
  change Q.map ((H.map ε.op).app (I.obj M) ≫ (H.obj (op K)).map (I.map (𝟙 M))) ≫
      c.inv.app (op K, M) =
    c.inv.app (op (ringedSiteRingComplex O), M) ≫
      (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
        (Y := (op (Q.obj K), Q.obj M)) ((Q.map ε).op, Q.map (𝟙 M)) at hcε
  simp only [Functor.map_id] at hcε
  have hcalc : Q.map (η.app M) ≫ Q.map (a.inv.app (I.obj M)) ≫
      c.inv.app (op (ringedSiteRingComplex O), M) ≫
        (derivedInternalHom J O).map
          (X := (op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
          (Y := (op (Q.obj K), Q.obj M)) ((Q.map ε).op, 𝟙 (Q.obj M)) ≫
          θ.hom.app (Q.obj M) = D.unitOnComplex M := by
    rw [← Category.assoc (c.inv.app (op (ringedSiteRingComplex O), M)), ← hcε]
    rw [hθ]
    dsimp only [t, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Iso.symm_hom, cK, NatIso.ofComponents_hom_app, asIso_hom,
      Functor.isoWhiskerRight_inv, asIso_inv]
    simp only [Category.assoc, Iso.app_hom, Iso.inv_hom_id_app_assoc]
    change Q.map (η.app M) ≫ Q.map (a.inv.app (I.obj M)) ≫
      Q.map ((H.map ε.op).app (I.obj M)) ≫ Q.map (v.hom.app (I.obj M)) ≫
      d.app (I.obj M) ≫ f.hom.app (I.obj M) ≫
        D.completion.map (qη.inv.app M) = _
    rw [← Q.map_comp_assoc (a.inv.app (I.obj M)),
      ← Q.map_comp_assoc (a.inv.app (I.obj M) ≫ (H.map ε.op).app (I.obj M))]
    change Q.map (η.app M) ≫ Q.map (z.app (I.obj M)) ≫
      d.app (I.obj M) ≫ f.hom.app (I.obj M) ≫
        D.completion.map (qη.inv.app M) = _
    have hbase : Q.map (z.app (I.obj M)) ≫ d.app (I.obj M) ≫
        f.hom.app (I.obj M) = D.unitOnComplex (I.obj M) := by
      rw [hz]
      rfl
    rw [reassoc_of% hbase]
    have hg := congrArg (fun k ↦ k ≫ D.completion.map (qη.inv.app M))
      (hu M (I.obj M) (η.app M))
    rw [← Category.assoc (Q.map (η.app M)), hg]
    simp only [Category.assoc, ← D.completion.map_comp]
    change D.unitOnComplex M ≫ D.completion.map (qη.hom.app M ≫ qη.inv.app M) = _
    rw [qη.hom_inv_id_app M]
    exact (congrArg (fun k ↦ D.unitOnComplex M ≫ k)
      (D.completion.map_id (Q.obj M))).trans (Category.comp_id _)
  have hn := θ.hom.naturality eM.hom
  have hs' : (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
        (Y := (op (Q.obj (ringedSiteRingComplex O)), E)) (𝟙 _, eM.hom) ≫
      (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), E))
        (Y := (op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E) =
    (derivedInternalHom J O).map
          (X := (op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
          (Y := (op (Q.obj K), Q.obj M)) ((Q.map ε).op, 𝟙 (Q.obj M)) ≫ F.map eM.hom := by
    change (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
        (Y := (op (Q.obj (ringedSiteRingComplex O)), E)) (𝟙 _, eM.hom) ≫
      (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), E))
        (Y := (op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E) =
      (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
        (Y := (op (Q.obj K), Q.obj M)) ((Q.map ε).op, 𝟙 (Q.obj M)) ≫
      (derivedInternalHom J O).map
        (X := (op (Q.obj K), Q.obj M)) (Y := (op (Q.obj K), E)) (𝟙 _, eM.hom)
    rw [← (derivedInternalHom J O).map_comp,
      ← (derivedInternalHom J O).map_comp]
    congr 1
    ext <;> simp
  dsimp only [ringedCechCompletionUnit, RingedKoszulLimitPresentation.unit]
  rw [ringedDerivedHomUnit_factorization]
  simp only [Category.assoc]
  change eM.inv ≫ Q.map (η.app M) ≫ Q.map (a.inv.app (I.obj M)) ≫
      c.inv.app (op (ringedSiteRingComplex O), M) ≫
        (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
        (Y := (op (Q.obj (ringedSiteRingComplex O)), E)) (𝟙 _, eM.hom) ≫
          (derivedInternalHom J O).map
        (X := (op (Q.obj (ringedSiteRingComplex O)), E))
        (Y := (op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E) ≫ θ.hom.app E =
    eM.inv ≫ D.unitOnComplex M ≫ D.completion.map eM.hom
  rw [reassoc_of% hs', hn]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ eM.inv ≫ k ≫ D.completion.map eM.hom) hcalc

end CategoryTheory
