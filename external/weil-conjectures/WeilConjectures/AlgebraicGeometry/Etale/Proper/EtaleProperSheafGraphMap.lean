/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianSumMateSheafNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-! # The ordinary sheaf graph map for a proper and etale factorization -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar upperStar etaleLowerShriek

private theorem comparison_comp_aux
    {C D E : Type*} [Category C] [Category D] [Category E]
    {Lt : C ⥤ D} {Ut : D ⥤ C} {Rt : C ⥤ D}
    {Lb : D ⥤ E} {Ub : E ⥤ D} {Rb : D ⥤ E}
    {Li : C ⥤ E} {Ui : E ⥤ C} {Ri : C ⥤ E}
    (adjT : Lt ⊣ Ut) (ar : Ut ⊣ Rt) (ab : Lb ⊣ Ub) (br : Ub ⊣ Rb)
    (ai : Li ⊣ Ui) (ir : Ui ⊣ Ri) (x : Ui ≅ Ub ⋙ Ut)
    (r : Rt ⋙ Rb ≅ Ri) (M : C)
    (ct : Lt.obj M ⟶ Rt.obj M)
    (cb : Lb.obj (Lt.obj M) ⟶ Rb.obj (Lt.obj M))
    (ci : Li.obj M ⟶ Ri.obj M)
    (ht : adjT.unit.app M ≫ Ut.map ct ≫ ar.counit.app M = 𝟙 M)
    (hb : ab.unit.app (Lt.obj M) ≫ Ub.map cb ≫ br.counit.app (Lt.obj M) =
      𝟙 (Lt.obj M))
    (hi : ai.unit.app M ≫ Ui.map ci ≫ ir.counit.app M = 𝟙 M)
    (hr : x.inv.app (Ri.obj M) ≫ ir.counit.app M =
      Ut.map (Ub.map (r.inv.app M)) ≫
        Ut.map (br.counit.app (Rt.obj M)) ≫ ar.counit.app M)
    [Mono (ir.counit.app M)] :
    ((((adjT.comp ab).ofNatIsoRight x.symm).leftAdjointUniq ai).hom.app M ≫ ci) =
      cb ≫ Rb.map ct ≫ r.hom.app M := by
  have hinner : ab.unit.app (Lt.obj M) ≫
      Ub.map (cb ≫ Rb.map ct ≫ r.hom.app M ≫ r.inv.app M) ≫
        br.counit.app (Rt.obj M) = ct := by
    have he : cb ≫ Rb.map ct ≫ r.hom.app M ≫ r.inv.app M = cb ≫ Rb.map ct := by
      calc
        _ = (cb ≫ Rb.map ct) ≫ (r.hom.app M ≫ r.inv.app M) := by
          simp only [Category.assoc]
        _ = (cb ≫ Rb.map ct) ≫ 𝟙 _ := by rw [Iso.hom_inv_id_app]; rfl
        _ = _ := Category.comp_id _
    rw [he]
    simp only [Functor.map_comp, Category.assoc]
    have hn := br.counit.naturality ct
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn]
    rw [reassoc_of% hb]
  let a := (adjT.comp ab).ofNatIsoRight x.symm
  apply (a.homEquiv _ _).injective
  apply (cancel_mono (ir.counit.app M)).1
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit,
    Category.assoc]
  simp only [Category.assoc]
  rw [hi]
  simp only [a, Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  rw [← x.inv.naturality_assoc, hr]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, Category.assoc]
  rw [hinner]
  exact ht.symm

private theorem sum_comparison_counit
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (b : X ⟶ Y) [Etale b] [IsSeparated b]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance).unit.app M ≫
        (upperStar (ModuleCat.{u + 1} A) b).map
          (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b M) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b).counit.app M = 𝟙 M := by
  have h := congr_app (lowerStarUnit_comp_counit (ModuleCat.{u + 1} A) b) M
  have he : (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) b
      inferInstance).hom.app ((lowerStar (ModuleCat.{u + 1} A) b).obj M) ≫
        (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A)
          b inferInstance).counit.app M =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b).counit.app M :=
    Adjunction.leftAdjointUniq_hom_app_counit _ _ M
  rw [← he]
  rw [reassoc_of% (sum_comparison_unit A b M)]
  exact h

private noncomputable def graphComposition
    (A : Type (u + 1)) [CommRing A]
    {W P Z : Scheme.{u}} (t : W ⟶ P) [IsOpenImmersion t]
    (b : P ⟶ Z) [Etale b] (i : W ⟶ Z) [IsOpenImmersion i]
    (hi : i = t ≫ b) :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) t ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) i :=
  (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) t).comp
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance)).ofNatIsoRight
      (upperStarComp (ModuleCat.{u + 1} A) t b i hi).symm).leftAdjointUniq
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)

private theorem graphComposition_comparison
    (A : Type (u + 1)) [CommRing A]
    {W P Z : Scheme.{u}} (t : W ⟶ P) [IsOpenImmersion t]
    (b : P ⟶ Z) [Etale b] [IsSeparated b]
    (i : W ⟶ Z) [IsOpenImmersion i] (hi : i = t ≫ b)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (graphComposition A t b i hi).hom.app M ≫
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) t).obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) b).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) t).app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) t b i hi).hom.app M := by
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app M) :=
    isIso_upperStarLowerStarAdjunction_counit_app_of_isOpenImmersion
      (ModuleCat.{u + 1} A) i M
  have hm : Mono ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app M) :=
    IsIso.mono_of_iso _
  apply comparison_comp_aux.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1}
    (C := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
    (E := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Lt := openImmersionLowerShriek (ModuleCat.{u + 1} A) t)
    (Ut := upperStar (ModuleCat.{u + 1} A) t)
    (Rt := lowerStar (ModuleCat.{u + 1} A) t)
    (Lb := etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance)
    (Ub := upperStar (ModuleCat.{u + 1} A) b)
    (Rb := lowerStar (ModuleCat.{u + 1} A) b)
    (Li := openImmersionLowerShriek (ModuleCat.{u + 1} A) i)
    (Ui := upperStar (ModuleCat.{u + 1} A) i)
    (Ri := lowerStar (ModuleCat.{u + 1} A) i)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) t)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) t)
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (upperStarComp (ModuleCat.{u + 1} A) t b i hi)
    (lowerStarComp (ModuleCat.{u + 1} A) t b i hi) M
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) t).app M)
    (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) t).obj M))
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app M)
    ?_ ?_ ?_ ?_
  · exact unit_map_openImmersionLowerShriekToLowerStar_app_counit
      (ModuleCat.{u + 1} A) t M
  · exact sum_comparison_counit A b _
  · exact unit_map_openImmersionLowerShriekToLowerStar_app_counit
      (ModuleCat.{u + 1} A) i M
  · exact upperStarComp_inv_app_counit_app.{u + 2, u}
      (ModuleCat.{u + 1} A) t b M i hi

private theorem sum_comparison_naturality
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (b : X ⟶ Y) [Etale b] [IsSeparated b]
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (φ : M ⟶ N) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).map φ ≫
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b N =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b M ≫
        (lowerStar (ModuleCat.{u + 1} A) b).map φ := by
  apply ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [etaleLowerShriekToLowerStar, Equiv.apply_symm_apply]
  exact (lowerStarUnit (ModuleCat.{u + 1} A) b).naturality φ

private theorem leftAdjointUniq_transpose
    {C D E : Type*} [Category C] [Category D] [Category E]
    {S : C ⥤ D} {T : D ⥤ C} {V : D ⥤ E} {W : E ⥤ D}
    {J : C ⥤ E} {R : E ⥤ C}
    (s : S ⊣ T) (v : V ⊣ W) (j : J ⊣ R) (t : R ≅ W ⋙ T) (N : C) :
    v.unit.app (S.obj N) ≫ W.map
        ((((s.comp v).ofNatIsoRight t.symm).leftAdjointUniq j).hom.app N) =
      S.map (j.unit.app N ≫ t.hom.app (J.obj N)) ≫
        s.counit.app (W.obj (J.obj N)) := by
  apply (s.homEquiv _ _).injective
  rw [s.homEquiv_unit]
  have h := Adjunction.unit_leftAdjointUniq_hom_app ((s.comp v).ofNatIsoRight t.symm) j N
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc] at h
  have hn := t.inv.naturality
    ((((s.comp v).ofNatIsoRight t.symm).leftAdjointUniq j).hom.app N)
  dsimp only [Functor.comp_map] at hn
  rw [← hn] at h
  have h' := congrArg (fun z ↦ z ≫ t.hom.app (J.obj N)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h'
  have hr := (s.homEquiv _ _).apply_symm_apply (j.unit.app N ≫ t.hom.app (J.obj N))
  rw [Adjunction.homEquiv_counit] at hr
  simpa only [Functor.map_comp, Functor.comp_obj, Functor.id_obj, Category.assoc] using
    h'.trans hr.symm

private theorem graphComposition_transpose
    (A : Type (u + 1)) [CommRing A]
    {W P Z : Scheme.{u}} (t : W ⟶ P) [IsOpenImmersion t]
    (b : P ⟶ Z) [Etale b] (i : W ⟶ Z) [IsOpenImmersion i] (hi : i = t ≫ b)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) t).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) b).map
        ((graphComposition A t b i hi).hom.app M) =
      (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A) t b i hi.symm).app M := by
  rw [graphComposition, leftAdjointUniq_transpose]
  apply ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) t).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hl := ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) t).homEquiv _ _).apply_symm_apply
      ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) i).unit.app M ≫
        (upperStarComp (ModuleCat.{u + 1} A) t b i hi).hom.app _)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit] at hl
  rw [hl]
  symm
  simpa only [upperStarCompIso_eq_upperStarComp, Functor.id_obj, Functor.comp_obj] using
    unit_map_openImmersionLowerShriekBaseChange_app
      (ModuleCat.{u + 1} A) t b i hi.symm M

private theorem properSheaf_graph_map_aux
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    {f : W ⟶ Y} (hf : f = q ≫ v) (c : Compactification f)
    {P : Scheme.{u}} (t : W ⟶ P) [IsOpenImmersion t]
    (p : P ⟶ V) (b : P ⟶ c.Z) [Etale b] [IsSeparated b]
    (sq : IsPullback b p c.g v) (ht : c.i = t ≫ b) (hi : t ≫ b = c.i)
    (hq : q = t ≫ p)
    [IsIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) t)]
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      τ.app F ≫ (compactificationSheafToDirectImage A c).app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v f hf).hom.app F)
    (F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).homEquiv
        _ _ (τ.app F) ≫
      (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj F) =
      (lowerStarComp (ModuleCat.{u + 1} A) t p q hq).inv.app F ≫
      (lowerStar (ModuleCat.{u + 1} A) p).map
        ((asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) t)).inv.app F ≫
          (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A) t b c.i hi).app F) := by
  -- Align the factorization proofs before the calculation, keeping the base-change map opaque
  -- to kernel conversion when the helper is specialized to the concrete graph.
  cases Subsingleton.elim ht.symm hi
  let B := ModuleCat.{u + 1} A
  let M := (openImmersionLowerShriek B t).obj F
  let γ := (openImmersionLowerShriekToLowerStar B t).app F
  let κ := (asIso (openImmersionLowerShriekToLowerStar B t)).inv.app F
  let α := lowerStarComp B t p q hq
  let comp := graphComposition A t b c.i ht
  let a := α.inv.app F ≫ (lowerStar B p).map κ
  let θ := (mateEquiv (upperStarLowerStarAdjunction B p)
    (upperStarLowerStarAdjunction B c.g)
    (TwoSquare.mk _ _ _ _ (etaleLowerShriekBaseChangeIso A sq).hom))
  let τ₀ := (etaleLowerShriek B v inferInstance).map a ≫ θ.app M ≫
    (lowerStar B c.g).map (comp.hom.app F)
  let lbg := lowerStarComp B b c.g
  let lpv := lowerStarComp B p v (b ≫ c.g) sq.w
  let ltbg := lowerStarComp B t (b ≫ c.g) f
    (c.comm.trans ((congrArg (fun z ↦ z ≫ c.g) ht).trans (Category.assoc _ _ _)))
  let lig := lowerStarComp B c.i c.g f c.comm
  let lti := lowerStarComp B t b c.i ht
  let lqv := lowerStarComp B q v f hf
  have hassoc1 : (lowerStar B c.g).map (lti.hom.app F) ≫ lig.hom.app F =
      lbg.hom.app ((lowerStar B t).obj F) ≫ ltbg.hom.app F := by
    exact congr_app (lowerStarComp_assoc' B t b c.g c.i (b ≫ c.g) f ht rfl c.comm) F
  have hassoc2 : (lowerStar B v).map (α.hom.app F) ≫ lqv.hom.app F =
      lpv.hom.app ((lowerStar B t).obj F) ≫ ltbg.hom.app F := by
    exact congr_app (lowerStarComp_assoc' B t p v q (b ≫ c.g) f hq sq.w hf) F
  have hγ : a ≫ (lowerStar B p).map γ = α.inv.app F := by
    simp only [a, Category.assoc, ← Functor.map_comp]
    have hκγ : κ ≫ γ = 𝟙 _ := Iso.inv_hom_id_app _ F
    rw [hκγ, _root_.CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hθ : θ.app M ≫ (lowerStar B c.g).map
        (etaleLowerShriekToLowerStar B b M) ≫ lbg.hom.app M =
      etaleLowerShriekToLowerStar B v ((lowerStar B p).obj M) ≫ lpv.hom.app M :=
    cartesian_sum_mate_sheaf_normalization A p c.g b v sq M
  have h₀ : τ₀ ≫ (compactificationSheafToDirectImage A c).app F =
      etaleLowerShriekToLowerStar B v ((lowerStar B q).obj F) ≫ lqv.hom.app F := by
    dsimp only [τ₀, compactificationSheafToDirectImage, NatTrans.comp_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, graphComposition_comparison A t b c.i ht F]
    simp only [Functor.map_comp, Category.assoc]
    rw [hassoc1]
    have hn := lbg.hom.naturality γ
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn, reassoc_of% hθ]
    have hn' := lpv.hom.naturality γ
    dsimp only [Functor.comp_map] at hn'
    rw [← reassoc_of% hn']
    rw [reassoc_of% (sum_comparison_naturality A v a)]
    rw [← Functor.map_comp_assoc]
    rw [hγ]
    rw [← hassoc2]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, _root_.CategoryTheory.Functor.map_id]
    rfl
  have hm : Mono ((compactificationSheafToDirectImage A c).app F) := by
    have := mono_openImmersionLowerShriekToLowerStar_app A c.i F
    dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
      Functor.whiskerRight_app]
    have hmap : Mono ((lowerStar B c.g).map
        ((openImmersionLowerShriekToLowerStar B c.i).app F)) :=
      Functor.map_mono (lowerStar B c.g) _
    have hcomp : Mono ((lowerStarComp B c.i c.g f c.comm).hom.app F) :=
      IsIso.mono_of_iso _
    exact mono_comp' hmap hcomp
  have hτ₀ : τ.app F = τ₀ := by
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app F)).1
    exact (hτ F).trans h₀.symm
  rw [hτ₀]
  have hxapp : ∀ G, IsIso ((baseChangeMap B sq.toCommSq).app G) := fun G ↦
    isIso_baseChangeMap_app_of_flat A sq G
  have hx : IsIso (baseChangeMap B sq.toCommSq) := NatIso.isIso_of_isIso_app _
  have hu := sum_mate_unit
    (etaleLowerShriekUpperStarAdjunction B v inferInstance)
    (upperStarLowerStarAdjunction B c.g)
    (upperStarLowerStarAdjunction B p)
    (etaleLowerShriekUpperStarAdjunction B b inferInstance)
    (asIso (baseChangeMap B sq.toCommSq)) M
  change (etaleLowerShriekUpperStarAdjunction B v inferInstance).unit.app
      ((lowerStar B p).obj M) ≫ (upperStar B v).map (θ.app M) ≫
        (baseChangeMap B sq.toCommSq).app
          ((etaleLowerShriek B b inferInstance).obj M) =
    (lowerStar B p).map
      ((etaleLowerShriekUpperStarAdjunction B b inferInstance).unit.app M) at hu
  simp only [τ₀, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [(etaleLowerShriekUpperStarAdjunction B v inferInstance).unit_naturality_assoc a]
  have hn := (baseChangeMap B sq.toCommSq).naturality (comp.hom.app F)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  change a ≫
    (etaleLowerShriekUpperStarAdjunction B v inferInstance).unit.app
      ((lowerStar B p).obj M) ≫ (upperStar B v).map (θ.app M) ≫
        (baseChangeMap B sq.toCommSq).app
          ((etaleLowerShriek B b inferInstance).obj M) ≫
        (lowerStar B p).map ((upperStar B b).map (comp.hom.app F)) = _
  rw [reassoc_of% hu]
  simp only [← Functor.map_comp]
  rw [graphComposition_transpose A t b c.i ht F]
  simp only [a, Functor.map_comp, Category.assoc]
  rfl

/-- The normalized proper-support map transposes to the ordinary clopen-graph map.
Source: Stacks Project, Tags 0F7B and 0F4L; SGA 4 XVII 6.2.11.
(blueprint: lem-pur-proper-sheaf-graph-map).

Proof in words: factor q_* through the direct image of its proper clopen graph,
identify that direct image with graph extension by zero, and apply the Cartesian
etale sum mate followed by the canonical composition of open and etale extension.
The comparison maps commute with this composition: after transposing, their unit
identities and the conjugate direct-image composition identity reduce the claim
to the identity of F. Cartesian sum mate normalization and direct-image
associativity now give the required normalization of the constructed map.
Extension by zero into direct image is monic, so hτ identifies τ with this map.
Finally the unit identity for the Cartesian sum mate computes its transpose,
and left-adjoint uniqueness identifies the remaining unit with open extension
base change. These categorical identities also cover empty graphs and zero
coefficients. -/
theorem properSheaf_graph_map
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    {f : W ⟶ Y} (hf : f = q ≫ v) (c : Compactification f)
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      τ.app F ≫ (compactificationSheafToDirectImage A c).app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v f hf).hom.app F)
    (F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).homEquiv
        _ _ (τ.app F) ≫
      (baseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj F) =
      (lowerStarComp (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c)
        (pullback.snd c.g v) q (ProperGraphTransfer.graph_snd q v hf c).symm).inv.app F ≫
      (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).map
        ((asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
          (ProperGraphTransfer.graph q v hf c))).inv.app F ≫
          (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A)
            (ProperGraphTransfer.graph q v hf c) (pullback.fst c.g v) c.i
            (ProperGraphTransfer.graph_fst q v hf c)).app F) := by
  exact properSheaf_graph_map_aux A q v hf c
    (ProperGraphTransfer.graph q v hf c) (pullback.snd c.g v) (pullback.fst c.g v)
    (IsPullback.of_hasPullback c.g v) (ProperGraphTransfer.graph_fst q v hf c).symm
    (ProperGraphTransfer.graph_fst q v hf c)
    (ProperGraphTransfer.graph_snd q v hf c).symm τ hτ F

end AlgebraicGeometry.Etale
