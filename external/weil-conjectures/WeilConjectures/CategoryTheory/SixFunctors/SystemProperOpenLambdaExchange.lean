/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Open restriction of the intrinsic proper/open comparison

Source: Stacks 0F7B and 07A7; the normalization calculation for the intrinsic
proper/open lambda (blueprint: lem-sf-system-proper-open-lambda-exchange). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

open CategoryTheory AlgebraicGeometry
namespace CategoryTheory

/-- A natural inverse-open-unit normalization of an exchange map.
Source: Stacks 07A7 (blueprint: lem-sf-system-proper-open-lambda-exchange). -/
def OpenExchangeUnitFormula
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Jk : A ⥤ B) (Rp : B ⥤ D) (Pi : D ⥤ C) (Pk : B ⥤ A) (Rr : A ⥤ C)
    (uk : 𝟭 A ≅ Jk ⋙ Pk) (chi : Rp ⋙ Pi ⟶ Pk ⋙ Rr)
    (lam : (Jk ⋙ Rp) ⋙ Pi ≅ Rr) : Prop :=
  ∀ M : A, lam.hom.app M = chi.app (Jk.obj M) ≫ Rr.map (uk.inv.app M)

end CategoryTheory

section Categorical
variable {A B C D V : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category V]

private theorem mate_formula
    {Lp : D ⥤ B} {Rp : B ⥤ D} {Lr : C ⥤ A} {Rr : A ⥤ C}
    (ap : Lp ⊣ Rp) (ar : Lr ⊣ Rr) (Pi : D ⥤ C) (Pk : B ⥤ A)
    (t : Pi ⋙ Lr ⟶ Lp ⋙ Pk) (M : B) :
    (mateEquiv ap ar (TwoSquare.mk _ _ _ _ t)).app M =
      ar.unit.app (Pi.obj (Rp.obj M)) ≫ Rr.map (t.app (Rp.obj M)) ≫
        Rr.map (Pk.map (ap.counit.app M)) := by
  simp [mateEquiv]

private theorem composite_mate_formula
    (Lp : D ⥤ B) (Rp : B ⥤ D) (Pq : C ⥤ V) (Rq : V ⥤ C)
    (Ps : V ⥤ A) (Rs : A ⥤ V)
    (ap : Lp ⊣ Rp) (aq : Pq ⊣ Rq) (as_ : Ps ⊣ Rs)
    (Pi : D ⥤ C) (Pb : B ⥤ V) (Pk : B ⥤ A)
    (theta : Pi ⋙ Pq ⟶ Lp ⋙ Pb) (c : Pb ⋙ Ps ≅ Pk) (M : B) :
    let t : Pi ⋙ (Pq ⋙ Ps) ⟶ Lp ⋙ Pk :=
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight theta Ps ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Lp c.hom
    (mateEquiv ap (aq.comp as_) (TwoSquare.mk _ _ _ _ t)).app M =
      (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta)).app M ≫
        Rq.map (as_.unit.app (Pb.obj M)) ≫ Rq.map (Rs.map (c.hom.app M)) := by
  intro t
  rw [mate_formula, mate_formula]
  have hn := as_.unit.naturality (theta.app (Rp.obj M))
  have he := as_.unit.naturality (Pb.map (ap.counit.app M))
  have hc := c.hom.naturality (ap.counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn he hc
  simp only [t, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  have hn' := congrArg Rq.map hn
  have he' := congrArg Rq.map he
  have hc' := congrArg (fun f ↦ Rq.map (Rs.map f)) hc
  simp only [Functor.map_comp] at hn' he' hc'
  rw [← reassoc_of% hn', ← hc', ← reassoc_of% he']

private def SquareFactorFormula
    (Lp : D ⥤ B) (Lr : C ⥤ A) (Pq : C ⥤ V) (Ps : V ⥤ A)
    (Pi : D ⥤ C) (Pb : B ⥤ V) (Pk : B ⥤ A)
    (theta : Pi ⋙ Pq ⟶ Lp ⋙ Pb) (c : Pb ⋙ Ps ≅ Pk)
    (e : Lr ≅ Pq ⋙ Ps) (t : Pi ⋙ Lr ⟶ Lp ⋙ Pk) : Prop :=
  ∀ N : D, t.app N = e.hom.app (Pi.obj N) ≫
    Ps.map (theta.app N) ≫ c.hom.app (Lp.obj N)

private theorem factor_mate_formula
    (Lp : D ⥤ B) (Rp : B ⥤ D) (Lr : C ⥤ A) (Rr : A ⥤ C)
    (Pq : C ⥤ V) (Rq : V ⥤ C) (Ps : V ⥤ A) (Rs : A ⥤ V)
    (ap : Lp ⊣ Rp) (ar : Lr ⊣ Rr) (aq : Pq ⊣ Rq) (as_ : Ps ⊣ Rs)
    (Pi : D ⥤ C) (Pb : B ⥤ V) (Pk : B ⥤ A)
    (theta : Pi ⋙ Pq ⟶ Lp ⋙ Pb) (c : Pb ⋙ Ps ≅ Pk)
    (e : Lr ≅ Pq ⋙ Ps) (t : Pi ⋙ Lr ⟶ Lp ⋙ Pk)
    (ht : SquareFactorFormula Lp Lr Pq Ps Pi Pb Pk theta c e t) (M : B) :
    (mateEquiv ap ar (TwoSquare.mk _ _ _ _ t)).app M =
      (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta)).app M ≫
        Rq.map (as_.unit.app (Pb.obj M)) ≫
        (conjugateIsoEquiv (aq.comp as_) ar e).hom.app (Ps.obj (Pb.obj M)) ≫
        Rr.map (c.hom.app M) := by
  let t₀ : Pi ⋙ (Pq ⋙ Ps) ⟶ Lp ⋙ Pk :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight theta Ps ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Lp c.hom
  have he : TwoSquare.mk _ _ _ _ t =
      (TwoSquare.mk _ _ _ _ t₀).whiskerRight e.hom := by
    refine NatTrans.ext (funext fun N ↦ ?_)
    simpa only [t₀, TwoSquare.whiskerRight, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp] using ht N
  rw [he, mateEquiv_conjugateEquiv_vcomp]
  change (mateEquiv ap (aq.comp as_) (TwoSquare.mk _ _ _ _ t₀)).app M ≫
    (conjugateIsoEquiv (aq.comp as_) ar e).hom.app (Pk.obj M) = _
  rw [composite_mate_formula]
  simp only [Category.assoc]
  have hn := (conjugateIsoEquiv (aq.comp as_) ar e).hom.naturality (c.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]

private def OpenUnitCompositeFormula
    (Js : A ⥤ V) (Ps : V ⥤ A) (Jb : V ⥤ B) (Pb : B ⥤ V)
    (Jk : A ⥤ B) (Pk : B ⥤ A)
    (us : 𝟭 A ≅ Js ⋙ Ps) (ub : 𝟭 V ≅ Jb ⋙ Pb) (uk : 𝟭 A ≅ Jk ⋙ Pk)
    (d : Js ⋙ Jb ≅ Jk) (c : Pb ⋙ Ps ≅ Pk) : Prop :=
  ∀ M : A, us.hom.app M ≫ Ps.map (ub.hom.app (Js.obj M)) ≫
    c.hom.app (Jb.obj (Js.obj M)) = uk.hom.app M ≫ Pk.map (d.inv.app M)

private theorem open_unit_factorization
    (Js : A ⥤ V) (Ps : V ⥤ A) (Jb : V ⥤ B) (Pb : B ⥤ V)
    (Jk : A ⥤ B) (Pk : B ⥤ A)
    (us : 𝟭 A ≅ Js ⋙ Ps) (ub : 𝟭 V ≅ Jb ⋙ Pb) (uk : 𝟭 A ≅ Jk ⋙ Pk)
    (d : Js ⋙ Jb ≅ Jk) (c : Pb ⋙ Ps ≅ Pk)
    (he : OpenUnitCompositeFormula Js Ps Jb Pb Jk Pk us ub uk d c)
    (M : A) :
    Ps.map (Pb.map (d.inv.app M) ≫ ub.inv.app (Js.obj M)) ≫ us.inv.app M =
      c.hom.app (Jk.obj M) ≫ uk.inv.app M := by
  have hx : us.app M ≪≫ Ps.mapIso (ub.app (Js.obj M)) ≪≫
      (Pb ⋙ Ps).mapIso (d.app M) = uk.app M ≪≫ (c.app (Jk.obj M)).symm := by
    apply Iso.ext
    apply (cancel_mono (c.hom.app (Jk.obj M))).1
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.comp_map, Category.assoc, Iso.inv_hom_id_app]
    have hn := c.hom.naturality (d.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [hn, reassoc_of% (he M), ← Pk.map_comp, d.inv_hom_id_app, Pk.map_id,
      Category.comp_id]
  simpa only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_inv, Functor.comp_map, Functor.map_comp, Category.assoc]
    using congrArg Iso.inv hx

private theorem exchange_clopen_paste
    (Ps : V ⥤ A) (Rs : A ⥤ V) (Rq : V ⥤ C) (Rr : A ⥤ C)
    (as_ : Ps ⊣ Rs) (delta : Rs ⋙ Rq ≅ Rr)
    (Js : A ⥤ V) (us : 𝟭 A ≅ Js ⋙ Ps) (t : Js ≅ Rs)
    (ht : ∀ M : A, t.hom.app M = as_.homEquiv _ _ (us.inv.app M))
    (M : A) (H : V) (f : H ⟶ Js.obj M) (g : Ps.obj H ⟶ M)
    (hg : g = Ps.map f ≫ us.inv.app M) :
    Rq.map (as_.unit.app H) ≫ delta.hom.app (Ps.obj H) ≫ Rr.map g =
      Rq.map f ≫ Rq.map (t.hom.app M) ≫ delta.hom.app M := by
  rw [hg, Rr.map_comp]
  have hn := delta.hom.naturality (Ps.map f)
  have hu := delta.hom.naturality (us.inv.app M)
  have hf := as_.unit.naturality f
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map,
    Functor.id_obj] at hn hu hf
  rw [← reassoc_of% hn, ← hu, ← Rq.map_comp_assoc, ← hf, Rq.map_comp]
  rw [ht, Adjunction.homEquiv_unit, Rq.map_comp]
  simp only [Category.assoc]

private theorem cartesian_mate_generic
    (Ji : C ⥤ D) (Pi : D ⥤ C) (Jb : V ⥤ B) (Pb : B ⥤ V)
    (Pp : D ⥤ B) (Rp : B ⥤ D) (Pq : C ⥤ V) (Rq : V ⥤ C)
    (ai : Ji ⊣ Pi) (ab : Jb ⊣ Pb) (ap : Pp ⊣ Rp) (aq : Pq ⊣ Rq)
    (beta : Ji ⋙ Pp ≅ Pq ⋙ Jb) (theta : Pi ⋙ Pq ≅ Pp ⋙ Pb)
    (hbeta : ∀ M : C, ab.homEquiv _ _ (beta.inv.app M) =
      Pq.map (ai.unit.app M) ≫ theta.hom.app (Ji.obj M)) :
    (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta.hom)) =
      (conjugateIsoEquiv (ai.comp ap) (aq.comp ab) beta.symm).hom := by
  have hb : mateEquiv ai ab (TwoSquare.mk _ _ _ _ beta.inv) =
      TwoSquare.mk _ _ _ _ theta.hom := by
    apply mateEquiv_eq_of_unit
    intro M
    simpa only [Adjunction.homEquiv_unit] using (hbeta M).symm
  have hh := iterated_mateEquiv_conjugateEquiv ai ab aq ap
    (TwoSquare.mk _ _ _ _ beta.inv)
  rw [hb] at hh
  exact hh

private theorem iso_square_cancel
    {C : Type*} [Category C] {X Y Z W T U : C}
    (aa : X ≅ Y) (bb : Y ≅ Z) (cc : X ≅ W) (dd : W ≅ Z)
    (ee : Y ≅ T) (ff : X ≅ U) (gg : U ≅ T)
    (h₁ : aa.hom ≫ bb.hom = cc.hom ≫ dd.hom)
    (h₂ : aa.hom ≫ ee.hom = ff.hom ≫ gg.hom) :
    cc.inv ≫ ff.hom = dd.hom ≫ bb.inv ≫ ee.hom ≫ gg.inv := by
  have he : aa ≪≫ bb = cc ≪≫ dd := Iso.ext h₁
  have hi := congrArg Iso.inv he
  dsimp only [Iso.trans_inv] at hi
  have hj := congrArg (fun z ↦ aa.inv ≫ z ≫ gg.inv) h₂
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] at hj
  have hh : dd.inv ≫ cc.inv ≫ ff.hom = bb.inv ≫ ee.hom ≫ gg.inv := by
    rw [← Category.assoc, ← hi, Category.assoc, ← hj]
  have hv := congrArg (fun z ↦ dd.hom ≫ z) hh
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hv

private def RestrictIsoFormula
    (Js : A ⥤ V) (Jb : V ⥤ B) (Jk : A ⥤ B) (Pb : B ⥤ V)
    (d : Js ⋙ Jb ≅ Jk) (ub : 𝟭 V ≅ Jb ⋙ Pb) (rho : Jk ⋙ Pb ≅ Js) : Prop :=
  ∀ M : A, rho.hom.app M = Pb.map (d.inv.app M) ≫ ub.inv.app (Js.obj M)

private theorem restrict_formula
    (Js : A ⥤ V) (Jb : V ⥤ B) (Jk : A ⥤ B) (Pb : B ⥤ V)
    (d : Js ⋙ Jb ≅ Jk) (ub : 𝟭 V ≅ Jb ⋙ Pb) :
    RestrictIsoFormula Js Jb Jk Pb d ub
      (Functor.isoWhiskerRight d.symm Pb ≪≫ Functor.associator Js Jb Pb ≪≫
        Functor.isoWhiskerLeft Js ub.symm ≪≫ Functor.rightUnitor Js) := by
  intro M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Category.id_comp]
  have hid : ub.inv.app (Js.obj M) ≫ 𝟙 (Js.obj M) = ub.inv.app (Js.obj M) := by
    simpa only [Functor.id_obj] using Category.comp_id (ub.inv.app (Js.obj M))
  exact congrArg (fun z ↦ Pb.map (d.inv.app M) ≫ z) hid

private theorem transport_symm
    {I K : Type*} [Category K] (F : I → K) {x y : I} (e : x = y) :
    eqToIso (congrArg F e.symm) = (eqToIso (congrArg F e)).symm := by
  cases e
  rfl

private theorem lambda_assembly
    (Lp : D ⥤ B) (Rp : B ⥤ D) (Lr : C ⥤ A) (Rr : A ⥤ C)
    (Pq : C ⥤ V) (Rq : V ⥤ C) (Ps : V ⥤ A) (Rs : A ⥤ V)
    (ap : Lp ⊣ Rp) (ar : Lr ⊣ Rr) (aq : Pq ⊣ Rq) (as_ : Ps ⊣ Rs)
    (Pi : D ⥤ C) (Pb : B ⥤ V) (Pk : B ⥤ A)
    (Js : A ⥤ V) (Jb : V ⥤ B) (Jk : A ⥤ B)
    (us : 𝟭 A ≅ Js ⋙ Ps) (ub : 𝟭 V ≅ Jb ⋙ Pb) (uk : 𝟭 A ≅ Jk ⋙ Pk)
    (d : Js ⋙ Jb ≅ Jk) (c : Pb ⋙ Ps ≅ Pk)
    (e : Lr ≅ Pq ⋙ Ps) (theta : Pi ⋙ Pq ⟶ Lp ⋙ Pb)
    (t : Pi ⋙ Lr ⟶ Lp ⋙ Pk) (z : Rp ⋙ Pi ≅ Pb ⋙ Rq)
    (rho : Jk ⋙ Pb ≅ Js) (cl : Js ≅ Rs) (delta : Rs ⋙ Rq ≅ Rr)
    (ht : SquareFactorFormula Lp Lr Pq Ps Pi Pb Pk theta c e t)
    (hz : (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta)) = z.hom)
    (hu : OpenUnitCompositeFormula Js Ps Jb Pb Jk Pk us ub uk d c)
    (hrho : RestrictIsoFormula Js Jb Jk Pb d ub rho)
    (hcl : ∀ M : A, cl.hom.app M = as_.homEquiv _ _ (us.inv.app M))
    (hdelta : conjugateIsoEquiv (aq.comp as_) ar e = delta) :
    OpenExchangeUnitFormula Jk Rp Pi Pk Rr uk
      (mateEquiv ap ar (TwoSquare.mk _ _ _ _ t))
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Jk z ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight rho Rq ≪≫
        Functor.isoWhiskerRight cl Rq ≪≫ delta) := by
  intro M
  have hm := factor_mate_formula Lp Rp Lr Rr Pq Rq Ps Rs ap ar aq as_
    Pi Pb Pk theta c e t ht (Jk.obj M)
  rw [hz, hdelta] at hm
  have hf : c.hom.app (Jk.obj M) ≫ uk.inv.app M =
      Ps.map (rho.hom.app M) ≫ us.inv.app M := by
    rw [hrho M]
    exact (open_unit_factorization Js Ps Jb Pb Jk Pk us ub uk d c hu M).symm
  have hpaste := exchange_clopen_paste Ps Rs Rq Rr as_ delta Js us cl hcl
    M (Pb.obj (Jk.obj M)) (rho.hom.app M)
    (c.hom.app (Jk.obj M) ≫ uk.inv.app M) hf
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp]
  rw [hm]
  simp only [Functor.map_comp, Category.assoc] at hpaste ⊢
  rw [hpaste]

end Categorical

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {o : Operations l E} (c : Compositors l E o)

private def suppliedComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (e : fg = f ≫ g) : pull l E fg ≅ pull l E g ⋙ pull l E f :=
  e.symm ▸ c.pullComp f g

private theorem suppliedComp_rfl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    suppliedComp l E c f g (f ≫ g) rfl = c.pullComp f g := by rfl

private theorem suppliedComp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (e : fg = f ≫ g) :
    suppliedComp l E c f g fg e = eqToIso (congrArg (pull l E) e) ≪≫ c.pullComp f g := by
  subst fg
  simp only [suppliedComp_rfl, eqToIso_refl, Iso.refl_trans]

private theorem suppliedComp_assoc {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (M : System l E Z) :
    (suppliedComp l E c f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app M ≫
      (pull l E f).map ((suppliedComp l E c g h gh hgh).hom.app M) =
    (suppliedComp l E c fg h fgh hfgh).hom.app M ≫
      (suppliedComp l E c f g fg hfg).hom.app ((pull l E h).obj M) := by
  subst hfg hgh hfgh
  have hh := congr_app (congrArg Iso.hom
    (integralSystemCompositorAssociativity l E c f g h)) M
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at hh
  have he : (eqToIso (congrArg (pull l E) (Category.assoc f g h).symm)).hom.app M =
      (eqToIso (congrArg (pull l E) (Category.assoc f g h))).inv.app M := by rfl
  rw [he] at hh
  have hv := (Iso.eq_inv_comp
    ((eqToIso (congrArg (pull l E) (Category.assoc f g h))).app M)).1 hh
  rw [suppliedComp_rfl l E c g h, suppliedComp_rfl l E c (f ≫ g) h,
    suppliedComp_rfl l E c f g, suppliedComp_eq]
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.app_hom, Category.assoc] using hv

private theorem square_supplied_app {A B C D : Scheme.{u}}
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    (h : k ≫ p = r ≫ i) (N : System l E D) :
    (c.square l E k r p i h).hom.app N =
      (suppliedComp l E c r i (k ≫ p) h).inv.app N ≫ (c.pullComp k p).hom.app N := by
  have he : c.square l E k r p i h =
      (suppliedComp l E c r i (k ≫ p) h).symm ≪≫ c.pullComp k p := by
    rw [suppliedComp_eq]
    change (c.pullComp r i).symm ≪≫ eqToIso (congrArg (pull l E) h.symm) ≪≫
      c.pullComp k p = _
    rw [transport_symm (pull l E) h]
    simp only [Iso.trans_symm, Iso.trans_assoc]
  exact congr_app (congrArg Iso.hom he) N

private theorem square_factorization
    {A B C D V : Scheme.{u}} (s : A ⟶ V) (b : V ⟶ B) (q : V ⟶ C)
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    (hsb : s ≫ b = k) (hsq : s ≫ q = r) (hbq : q ≫ i = b ≫ p)
    (h : k ≫ p = r ≫ i) :
    SquareFactorFormula (pull l E p) (pull l E r) (pull l E q) (pull l E s)
      (pull l E i) (pull l E b) (pull l E k)
      (c.square l E b q p i hbq.symm).hom
      (suppliedComp l E c s b k hsb.symm).symm
      (suppliedComp l E c s q r hsq.symm) (c.square l E k r p i h).hom := by
  intro N
  let aa := (suppliedComp l E c s (b ≫ p) (k ≫ p)
    (by rw [← hsb, Category.assoc])).app N
  let bb := (pull l E s).mapIso
    ((suppliedComp l E c q i (b ≫ p) hbq.symm).app N)
  let cc := (suppliedComp l E c r i (k ≫ p) h).app N
  let dd := (suppliedComp l E c s q r hsq.symm).app ((pull l E i).obj N)
  let ee := (pull l E s).mapIso
    ((c.pullComp b p).app N)
  let ff := (c.pullComp k p).app N
  let gg := (suppliedComp l E c s b k hsb.symm).app ((pull l E p).obj N)
  have h₁ : aa.hom ≫ bb.hom = cc.hom ≫ dd.hom := by
    exact suppliedComp_assoc l E c s q i r (b ≫ p) (k ≫ p)
      hsq.symm hbq.symm h N
  have h₂ : aa.hom ≫ ee.hom = ff.hom ≫ gg.hom := by
    exact suppliedComp_assoc l E c s b p k (b ≫ p) (k ≫ p)
      hsb.symm rfl rfl N
  have hv := iso_square_cancel aa bb cc dd ee ff gg h₁ h₂
  simpa only [square_supplied_app, aa, bb, cc, dd, ee, ff, gg,
    Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc] using hv

private theorem square_flip {A B C D : Scheme.{u}}
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    (h : k ≫ p = r ≫ i) :
    (c.square l E k r p i h).hom = (c.square l E r k i p h.symm).inv := by
  simp only [Compositors.square, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv, Category.assoc]

private theorem cartesian_mate {B C D : Scheme.{u}} (a : OpenComparisons l E o c)
    (p : B ⟶ D) (i : C ⟶ D) [IsOpenImmersion i] :
    (properExchange l E o c (Limits.pullback.fst p i) (Limits.pullback.snd p i) p i
      (Limits.pullback.condition)) =
      (cartesianConjugate l E o c a p i).hom := by
  have hh := cartesian_mate_generic
    (Operations.shriek l E o i) (pull l E i)
    (Operations.shriek l E o (Limits.pullback.fst p i))
    (pull l E (Limits.pullback.fst p i))
    (pull l E p) (Operations.push l E o p)
    (pull l E (Limits.pullback.snd p i))
    (Operations.push l E o (Limits.pullback.snd p i))
    (o.extension i).adj (o.extension (Limits.pullback.fst p i)).adj
    (o.direct p).adj (o.direct (Limits.pullback.snd p i)).adj
    (a.beta (Limits.pullback.snd p i) (Limits.pullback.fst p i) i p
      Limits.pullback.condition.symm (IsPullback.of_hasPullback p i).flip)
    (c.square l E (Limits.pullback.fst p i) (Limits.pullback.snd p i)
      p i Limits.pullback.condition)
    (fun M ↦ by
      have ht := a.beta_transpose (Limits.pullback.snd p i) (Limits.pullback.fst p i)
        i p Limits.pullback.condition.symm (IsPullback.of_hasPullback p i).flip M
      rw [← square_flip l E c] at ht
      exact ht)
  exact hh

private theorem openCongr_refl {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : openCongr l E o (rfl : j = j) = Iso.refl _ := by
  apply Iso.ext
  ext M
  simp [openCongr, Adjunction.leftAdjointUniq, Adjunction.ofNatIsoRight]

private theorem open_comp_unit (a : OpenComparisons l E o c)
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] (M : System l E U) :
    (a.unit l E o c s).hom.app M ≫
        (pull l E s).map ((a.unit l E o c b).hom.app ((Operations.shriek l E o s).obj M)) ≫
        (c.pullComp s b).inv.app
          ((Operations.shriek l E o b).obj ((Operations.shriek l E o s).obj M)) =
      (a.unit l E o c (s ≫ b)).hom.app M ≫
        (pull l E (s ≫ b)).map ((c.openComp l E s b).inv.app M) := by
  simpa only [Compositors.openComp, OpenComparisons.unit,
    NatIso.ofComponents_hom_app, asIso_hom, Iso.symm_hom,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map, Category.assoc]
    using unit_conjugateEquiv ((o.extension s).adj.comp (o.extension b).adj)
      (o.extension (s ≫ b)).adj (c.openComp l E s b).inv M

private theorem supplied_open_comp_unit (a : OpenComparisons l E o c)
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (e : s ≫ b = k) :
    OpenUnitCompositeFormula
      (Operations.shriek l E o s) (pull l E s)
      (Operations.shriek l E o b) (pull l E b)
      (Operations.shriek l E o k) (pull l E k)
      (a.unit l E o c s) (a.unit l E o c b) (a.unit l E o c k)
      (c.openComp l E s b ≪≫ openCongr l E o e)
      (suppliedComp l E c s b k e.symm).symm := by
  intro M
  dsimp only [OpenUnitCompositeFormula, Iso.symm_hom]
  rw [suppliedComp_eq]
  subst k
  simpa only [openCongr_refl, Iso.trans_refl, eqToIso_refl, Iso.refl_trans]
    using open_comp_unit l E c a s b M

private theorem push_factorization {A V C : Scheme.{u}}
    (s : A ⟶ V) (q : V ⟶ C) (r : A ⟶ C) (e : s ≫ q = r) :
    conjugateIsoEquiv ((o.direct q).adj.comp (o.direct s).adj) (o.direct r).adj
      (eqToIso (congrArg (pull l E) e.symm) ≪≫ c.pullComp s q) =
        c.pushComp l E s q ≪≫ eqToIso (congrArg (Operations.push l E o) e) := by
  subst r
  simp [Compositors.pushComp]

private theorem supplied_push_factorization {A V C : Scheme.{u}}
    (s : A ⟶ V) (q : V ⟶ C) (r : A ⟶ C) (e : s ≫ q = r) :
    conjugateIsoEquiv ((o.direct q).adj.comp (o.direct s).adj) (o.direct r).adj
      (suppliedComp l E c s q r e.symm) =
        c.pushComp l E s q ≪≫ eqToIso (congrArg (Operations.push l E o) e) := by
  rw [suppliedComp_eq]
  exact push_factorization l E c s q r e

private theorem restrictFactor_formula (a : OpenComparisons l E o c)
    {A B C D : Scheme.{u}}
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    RestrictIsoFormula
      (Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h))
      (Operations.shriek l E o (Limits.pullback.fst p i)) (Operations.shriek l E o k)
      (pull l E (Limits.pullback.fst p i))
      (c.openComp l E (ProEtale.StrictTower.squareLift k r p i h)
        (Limits.pullback.fst p i) ≪≫ openCongr l E o (Limits.pullback.lift_fst k r h))
      (a.unit l E o c (Limits.pullback.fst p i)) (restrictFactor l E o c a k r p i h) := by
  exact restrict_formula
    (Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h))
    (Operations.shriek l E o (Limits.pullback.fst p i)) (Operations.shriek l E o k)
    (pull l E (Limits.pullback.fst p i))
    (c.openComp l E (ProEtale.StrictTower.squareLift k r p i h)
      (Limits.pullback.fst p i) ≪≫ openCongr l E o (Limits.pullback.lift_fst k r h))
    (a.unit l E o c (Limits.pullback.fst p i))

/-- The prescribed lambda is proper exchange followed by the inverse open unit.
Source: Stacks 0F7B (restriction of proper/open interchange) and 07A7 (mates)
(blueprint: lem-sf-system-proper-open-lambda-exchange).

Proof: write s for the canonical clopen lift, b and q for the two projections of
B times_D C. Associativity of the recorded pullback compositors identifies the
square for k,r,p,i with the square for b,q,p,i followed by restriction along s,
using s b = k and s q = r. Take the proper-adjunction mates. The first mate is
cartesianConjugate: the beta inverse transpose and the two open units identify
its open mate with the inverse-image square; iterating mates equals conjugation
under the composite adjunction. The second mate inserts the s-direct-image unit
and the direct-image compositor. On k-extension objects the inverse k-unit,
transported through the canonical open compositor, becomes restrictFactor followed
by the inverse s-open unit. By clopen_transpose, the latter unit is precisely the
transpose of the clopen comparison. The resulting factors are, in order,
cartesianConjugate, restrictFactor, clopen, pushComp and equality transport,
which is the definition of properOpenLambda. This is an equality of unbounded
system maps before evaluation. For identity arrows it is the adjunction triangle;
for an empty open, the same unit and counit equalities apply to the zero category. -/
theorem systemProperOpenLambdaExchange
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c)
    {A B C D : Scheme.{u}}
    (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    OpenExchangeUnitFormula (Operations.shriek l E o k) (Operations.push l E o p)
      (pull l E i) (pull l E k) (Operations.push l E o r) (a.unit l E o c k)
      (properExchange l E o c k r p i h) (properOpenLambda l E o c a k r p i h) := by
  exact lambda_assembly
    (pull l E p) (Operations.push l E o p) (pull l E r) (Operations.push l E o r)
    (pull l E (Limits.pullback.snd p i)) (Operations.push l E o (Limits.pullback.snd p i))
    (pull l E (ProEtale.StrictTower.squareLift k r p i h))
    (Operations.push l E o (ProEtale.StrictTower.squareLift k r p i h))
    (o.direct p).adj (o.direct r).adj (o.direct (Limits.pullback.snd p i)).adj
    (o.direct (ProEtale.StrictTower.squareLift k r p i h)).adj
    (pull l E i) (pull l E (Limits.pullback.fst p i)) (pull l E k)
    (Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h))
    (Operations.shriek l E o (Limits.pullback.fst p i)) (Operations.shriek l E o k)
    (a.unit l E o c (ProEtale.StrictTower.squareLift k r p i h))
    (a.unit l E o c (Limits.pullback.fst p i)) (a.unit l E o c k)
    (c.openComp l E (ProEtale.StrictTower.squareLift k r p i h) (Limits.pullback.fst p i) ≪≫
      openCongr l E o (Limits.pullback.lift_fst k r h))
    (suppliedComp l E c (ProEtale.StrictTower.squareLift k r p i h)
      (Limits.pullback.fst p i) k (Limits.pullback.lift_fst k r h).symm).symm
    (suppliedComp l E c (ProEtale.StrictTower.squareLift k r p i h)
      (Limits.pullback.snd p i) r (Limits.pullback.lift_snd k r h).symm)
    (c.square l E (Limits.pullback.fst p i) (Limits.pullback.snd p i) p i
      Limits.pullback.condition).hom (c.square l E k r p i h).hom
    (cartesianConjugate l E o c a p i) (restrictFactor l E o c a k r p i h)
    (a.clopen (ProEtale.StrictTower.squareLift k r p i h))
    (c.pushComp l E (ProEtale.StrictTower.squareLift k r p i h) (Limits.pullback.snd p i) ≪≫
      eqToIso (congrArg (Operations.push l E o) (Limits.pullback.lift_snd k r h)))
    (square_factorization l E c (ProEtale.StrictTower.squareLift k r p i h)
      (Limits.pullback.fst p i) (Limits.pullback.snd p i) k r p i
      (Limits.pullback.lift_fst k r h) (Limits.pullback.lift_snd k r h)
      Limits.pullback.condition.symm h)
    (cartesian_mate l E c a p i)
    (supplied_open_comp_unit l E c a (ProEtale.StrictTower.squareLift k r p i h)
      (Limits.pullback.fst p i) k (Limits.pullback.lift_fst k r h))
    (restrictFactor_formula l E c a k r p i h)
    (fun M ↦ a.clopen_transpose (ProEtale.StrictTower.squareLift k r p i h) M)
    (supplied_push_factorization l E c (ProEtale.StrictTower.squareLift k r p i h)
      (Limits.pullback.snd p i) r (Limits.pullback.lift_snd k r h))

end WeilConjectures.IntegralSystemRealization
