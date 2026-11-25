/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import all WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import all WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.NormalizedScalarSectionFamily
public import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle

/-! # Scalar extension and geometric exchange

All functors are the existing ordinary unbounded internal-module derived functors.
The balancing maps are specified by their universal computation-counit normalization.
The direct-image maps are their actual mates, without an invertibility assumption.

## References

* Stacks Project, Tags 07A7 and 0E47
-/

@[expose] public noncomputable section

set_option linter.all false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

attribute [local irreducible] CategoryTheory.mateEquiv
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedFunctor
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullbackComposition
  AlgebraicGeometry.ProEtale.QuotientChange.scalarSectionPullComparison

private theorem conjugate_route
    {C : Type*} [Category* C] {A B X Y : C}
    (s : A ≅ B) (t : X ≅ Y) (f : A ⟶ X) (g : B ⟶ Y)
    (h : f ≫ t.hom = s.hom ≫ g) : s.inv ≫ f ≫ t.hom = g := by
  rw [h, Iso.inv_hom_id_assoc]

private theorem reverse_compositor
    {C : Type*} [Category* C] {T : Type*} (G : T → C)
    {x y : T} {U V : C} (w : x = y) (b : G y ≅ U) (a : G x ≅ V) :
    (eqToIso (congrArg G w) ≪≫ b).symm ≪≫ a =
      b.symm ≪≫ eqToIso (congrArg G w.symm) ≪≫ a := by
  simp only [Iso.trans_symm, Iso.trans_assoc]
  exact congrArg (fun e ↦ b.symm ≪≫ e ≪≫ a) (scalarSquare_eqToIso_symm G w)

namespace CategoryTheory

end CategoryTheory

private theorem mate_rectangle
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {f : A₀ ⥤ A₁} {rf : A₁ ⥤ A₀} {g : A₂ ⥤ A₃} {rg : A₃ ⥤ A₂}
    {fb : B₀ ⥤ B₁} {rfb : B₁ ⥤ B₀} {gb : B₂ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (af : f ⊣ rf) (ag : g ⊣ rg) (bf : fb ⊣ rfb) (bg : gb ⊣ rgb)
    {a : A₁ ⥤ A₃} {c : A₀ ⥤ A₂} {ab : B₁ ⥤ B₃} {cb : B₀ ⥤ B₂}
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₂ : A₂ ⥤ B₂} {T₃ : A₃ ⥤ B₃}
    (lf : T₀ ⋙ fb ⟶ f ⋙ T₁) (lg : T₂ ⋙ gb ⟶ g ⋙ T₃)
    (la : T₁ ⋙ ab ⟶ a ⋙ T₃) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (sa : c ⋙ g ⟶ f ⋙ a) (sb : cb ⋙ gb ⟶ fb ⋙ ab)
    (coh : ∀ M, gb.map (lc.app M) ≫ lg.app (c.obj M) ≫ T₃.map (sa.app M) =
      sb.app (T₀.obj M) ≫ ab.map (lf.app M) ≫ la.app (f.obj M))
    (J : A₁) :
    cb.map ((mateEquiv af bf (TwoSquare.mk _ _ _ _ lf)).natTrans.app J) ≫
        (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans.app (T₁.obj J) ≫
        rgb.map (la.app J) =
      lc.app (rf.obj J) ≫
        T₂.map ((mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans.app J) ≫
        (mateEquiv ag bg (TwoSquare.mk _ _ _ _ lg)).natTrans.app (a.obj J) := by
  let r := (mateEquiv af bf (TwoSquare.mk _ _ _ _ lf)).natTrans
  let t := (mateEquiv ag bg (TwoSquare.mk _ _ _ _ lg)).natTrans
  let e := (mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans
  let eb := (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans
  have hr := mateEquiv_counit af bf (TwoSquare.mk _ _ _ _ lf) J
  have ht := mateEquiv_counit ag bg (TwoSquare.mk _ _ _ _ lg) (a.obj J)
  have he := mateEquiv_counit af ag (TwoSquare.mk _ _ _ _ sa) J
  have heb := mateEquiv_counit bf bg (TwoSquare.mk _ _ _ _ sb) (T₁.obj J)
  change fb.map (r.app J) ≫ bf.counit.app _ = _ at hr
  change gb.map (t.app (a.obj J)) ≫ bg.counit.app _ = _ at ht
  change g.map (e.app J) ≫ ag.counit.app _ = _ at he
  change gb.map (eb.app (T₁.obj J)) ≫ bg.counit.app _ = _ at heb
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at hr ht he heb
  apply (bg.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp, Category.assoc]
  change gb.map (cb.map (r.app J)) ≫ gb.map (eb.app (T₁.obj J)) ≫
      gb.map (rgb.map (la.app J)) ≫ bg.counit.app _ =
    gb.map (lc.app (rf.obj J)) ≫ gb.map (T₂.map (e.app J)) ≫
      gb.map (t.app (a.obj J)) ≫ bg.counit.app _
  have hn := bg.counit.naturality (la.app J)
  change gb.map (rgb.map (la.app J)) ≫ bg.counit.app _ =
    bg.counit.app _ ≫ la.app J at hn
  rw [hn, reassoc_of% heb, ht]
  have ns := sb.naturality (r.app J)
  change gb.map (cb.map (r.app J)) ≫ sb.app _ =
    sb.app _ ≫ ab.map (fb.map (r.app J)) at ns
  rw [reassoc_of% ns, ← ab.map_comp_assoc, hr, ab.map_comp]
  have nl := la.naturality (af.counit.app J)
  change ab.map (T₁.map (af.counit.app J)) ≫ la.app J =
    la.app _ ≫ T₃.map (a.map (af.counit.app J)) at nl
  simp only [Category.assoc]
  rw [nl]
  have ng := lg.naturality (e.app J)
  change gb.map (T₂.map (e.app J)) ≫ lg.app _ =
    lg.app _ ≫ T₃.map (g.map (e.app J)) at ng
  rw [reassoc_of% ng, ← T₃.map_comp, he, T₃.map_comp]
  rw [reassoc_of% coh]
  rfl

private theorem mate_rectangle_of_eq
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {f : A₀ ⥤ A₁} {rf : A₁ ⥤ A₀} {g : A₂ ⥤ A₃} {rg : A₃ ⥤ A₂}
    {fb : B₀ ⥤ B₁} {rfb : B₁ ⥤ B₀} {gb : B₂ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (af : f ⊣ rf) (ag : g ⊣ rg) (bf : fb ⊣ rfb) (bg : gb ⊣ rgb)
    {a : A₁ ⥤ A₃} {c : A₀ ⥤ A₂} {ab : B₁ ⥤ B₃} {cb : B₀ ⥤ B₂}
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₂ : A₂ ⥤ B₂} {T₃ : A₃ ⥤ B₃}
    (lf : T₀ ⋙ fb ⟶ f ⋙ T₁) (lg : T₂ ⋙ gb ⟶ g ⋙ T₃)
    (la : T₁ ⋙ ab ⟶ a ⋙ T₃) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (sa : c ⋙ g ⟶ f ⋙ a) (sb : cb ⋙ gb ⟶ fb ⋙ ab)
    (coh : ∀ M, gb.map (lc.app M) ≫ lg.app (c.obj M) ≫ T₃.map (sa.app M) =
      sb.app (T₀.obj M) ≫ ab.map (lf.app M) ≫ la.app (f.obj M))
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb)
    (e : rf ⋙ c ⟶ a ⋙ rg) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (hr : r = (mateEquiv af bf (TwoSquare.mk _ _ _ _ lf)).natTrans)
    (ht : t = (mateEquiv ag bg (TwoSquare.mk _ _ _ _ lg)).natTrans)
    (he : e = (mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans)
    (heb : eb = (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans)
    (J : A₁) :
    mateRouteLeft cb r eb la J = mateRouteRight T₂ lc e t J := by
  subst r
  subst t
  subst e
  subst eb
  exact mate_rectangle af ag bf bg lf lg la lc sa sb coh J

private theorem mate_transport
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {f : A₀ ⥤ A₁} {rf : A₁ ⥤ A₀} {g : A₂ ⥤ A₃} {rg : A₃ ⥤ A₂}
    {fb : B₀ ⥤ B₁} {rfb : B₁ ⥤ B₀} {gb : B₂ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (af : f ⊣ rf) (ag : g ⊣ rg) (bf : fb ⊣ rfb) (bg : gb ⊣ rgb)
    {a : A₁ ⥤ A₃} {c : A₀ ⥤ A₂} {ab : B₁ ⥤ B₃} {cb : B₀ ⥤ B₂}
    {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂} {E₃ : A₃ ⥤ B₃}
    (jf : f ⋙ E₁ ≅ E₀ ⋙ fb) (jg : g ⋙ E₃ ≅ E₂ ⋙ gb)
    (uf : rf ⋙ E₀ ≅ E₁ ⋙ rfb) (ug : rg ⋙ E₂ ≅ E₃ ⋙ rgb)
    (hf : (mateEquiv af bf (TwoSquare.mk _ _ _ _ jf.inv)).natTrans = uf.hom)
    (hg : (mateEquiv ag bg (TwoSquare.mk _ _ _ _ jg.inv)).natTrans = ug.hom)
    (p : c ⋙ E₂ ≅ E₀ ⋙ cb) (q : a ⋙ E₃ ≅ E₁ ⋙ ab)
    (sa : c ⋙ g ⟶ f ⋙ a) (sb : cb ⋙ gb ⟶ fb ⋙ ab)
    (coh : ∀ M, E₃.map (sa.app M) ≫ q.hom.app (f.obj M) ≫
      ab.map (jf.hom.app M) = jg.hom.app (c.obj M) ≫
        gb.map (p.hom.app M) ≫ sb.app (E₀.obj M)) (J : A₁) :
    E₂.map ((mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans.app J) ≫
        ug.hom.app (a.obj J) ≫ rgb.map (q.hom.app J) =
      p.hom.app (rf.obj J) ≫ cb.map (uf.hom.app J) ≫
        (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans.app (E₁.obj J) := by
  have hc (M : A₀) :
      gb.map (p.inv.app M) ≫ jg.inv.app (c.obj M) ≫ E₃.map (sa.app M) =
        sb.app (E₀.obj M) ≫ ab.map (jf.inv.app M) ≫ q.inv.app (f.obj M) := by
    have he := congrArg (fun t ↦ gb.map (p.inv.app M) ≫
      jg.inv.app (c.obj M) ≫ t ≫ ab.map (jf.inv.app M) ≫ q.inv.app (f.obj M)) (coh M)
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app] at he
    simpa [Category.assoc] using he
  have he := mate_rectangle af ag bf bg jf.inv jg.inv q.inv p.inv sa sb hc J
  rw [hf, hg] at he
  have he' := congrArg (fun t ↦ p.hom.app (rf.obj J) ≫ t ≫ rgb.map (q.hom.app J)) he
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id_app] at he'
  simpa [Category.assoc] using he'.symm

private def squareCoherence
    {A B C D A' B' C' D' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* A'] [Category* B'] [Category* C'] [Category* D']
    {E₀ : A ⥤ A'} {E₁ : B ⥤ B'} {E₂ : C ⥤ C'} {E₃ : D ⥤ D'}
    {f : A ⥤ B} {a : B ⥤ D} {c : A ⥤ C} {g : C ⥤ D}
    {fb : A' ⥤ B'} {ab : B' ⥤ D'} {cb : A' ⥤ C'} {gb : C' ⥤ D'}
    (jf : f ⋙ E₁ ≅ E₀ ⋙ fb) (ja : a ⋙ E₃ ≅ E₁ ⋙ ab)
    (jc : c ⋙ E₂ ≅ E₀ ⋙ cb) (jg : g ⋙ E₃ ≅ E₂ ⋙ gb)
    (sa : c ⋙ g ⟶ f ⋙ a) (sb : cb ⋙ gb ⟶ fb ⋙ ab) (M : A) : Prop :=
  E₃.map (sa.app M) ≫ ja.hom.app (f.obj M) ≫ ab.map (jf.hom.app M) =
    jg.hom.app (c.obj M) ≫ gb.map (jc.hom.app M) ≫ sb.app (E₀.obj M)

private def compositionCoherence
    {A B D A' B' D' : Type*}
    [Category* A] [Category* B] [Category* D]
    [Category* A'] [Category* B'] [Category* D']
    {E₀ : A ⥤ A'} {E₁ : B ⥤ B'} {E₃ : D ⥤ D'}
    {f : A ⥤ B} {a : B ⥤ D} {h : A ⥤ D}
    {fb : A' ⥤ B'} {ab : B' ⥤ D'} {hb : A' ⥤ D'}
    (jf : f ⋙ E₁ ≅ E₀ ⋙ fb) (ja : a ⋙ E₃ ≅ E₁ ⋙ ab)
    (jh : h ⋙ E₃ ≅ E₀ ⋙ hb) (x : h ≅ f ⋙ a) (xb : hb ≅ fb ⋙ ab)
    (M : A) : Prop :=
  jh.hom.app M ≫ xb.hom.app (E₀.obj M) =
    E₃.map (x.hom.app M) ≫ ja.hom.app (f.obj M) ≫ ab.map (jf.hom.app M)

private theorem compositionCoherence_eq
    {A C D A' C' D' : Type*}
    [Category* A] [Category* C] [Category* D]
    [Category* A'] [Category* C'] [Category* D']
    {E₀ : A ⥤ A'} {E₂ : C ⥤ C'} {E₃ : D ⥤ D'}
    {c : A ⥤ C} {g : C ⥤ D} {cb : A' ⥤ C'} {gb : C' ⥤ D'}
    {I : Type*} (H : I → A ⥤ D) (Hb : I → A' ⥤ D')
    (j : ∀ i, H i ⋙ E₃ ≅ E₀ ⋙ Hb i)
    (jc : c ⋙ E₂ ≅ E₀ ⋙ cb) (jg : g ⋙ E₃ ≅ E₂ ⋙ gb)
    {i k : I} (w : i = k) (y : H k ≅ c ⋙ g) (yb : Hb k ≅ cb ⋙ gb)
    (hy : ∀ M, compositionCoherence jc jg (j k) y yb M) :
    ∀ M, compositionCoherence jc jg (j i)
      (eqToIso (congrArg H w) ≪≫ y) (eqToIso (congrArg Hb w) ≪≫ yb) M := by
  subst k
  simpa only [eqToIso_refl, Iso.refl_trans] using hy

private theorem mate_transport_of_eq
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {f : A₀ ⥤ A₁} {rf : A₁ ⥤ A₀} {g : A₂ ⥤ A₃} {rg : A₃ ⥤ A₂}
    {fb : B₀ ⥤ B₁} {rfb : B₁ ⥤ B₀} {gb : B₂ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (af : f ⊣ rf) (ag : g ⊣ rg) (bf : fb ⊣ rfb) (bg : gb ⊣ rgb)
    {a : A₁ ⥤ A₃} {c : A₀ ⥤ A₂} {ab : B₁ ⥤ B₃} {cb : B₀ ⥤ B₂}
    {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂} {E₃ : A₃ ⥤ B₃}
    (jf : f ⋙ E₁ ≅ E₀ ⋙ fb) (jg : g ⋙ E₃ ≅ E₂ ⋙ gb)
    (uf : rf ⋙ E₀ ≅ E₁ ⋙ rfb) (ug : rg ⋙ E₂ ≅ E₃ ⋙ rgb)
    (hf : (mateEquiv af bf (TwoSquare.mk _ _ _ _ jf.inv)).natTrans = uf.hom)
    (hg : (mateEquiv ag bg (TwoSquare.mk _ _ _ _ jg.inv)).natTrans = ug.hom)
    (p : c ⋙ E₂ ≅ E₀ ⋙ cb) (q : a ⋙ E₃ ≅ E₁ ⋙ ab)
    (sa : c ⋙ g ⟶ f ⋙ a) (sb : cb ⋙ gb ⟶ fb ⋙ ab)
    (coh : ∀ M, squareCoherence jf q p jg sa sb M)
    (e : rf ⋙ c ⟶ a ⋙ rg) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (he : e = (mateEquiv af ag (TwoSquare.mk _ _ _ _ sa)).natTrans)
    (heb : eb = (mateEquiv bf bg (TwoSquare.mk _ _ _ _ sb)).natTrans)
    (J : A₁) :
    mateRouteLeft E₂ e ug.hom q.hom J =
      mateRouteRight cb p.hom uf.hom eb J := by
  subst e
  subst eb
  exact mate_transport af ag bf bg jf jg uf ug hf hg p q sa sb coh J

private theorem left_route_algebra
    {A B C A' B' C' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    (E : C ⥤ C') (EA : A ⥤ A') (EB : B ⥤ B')
    (P : A ⥤ C) (Q : B ⥤ C) (p : A' ⥤ C') (q : B' ⥤ C')
    (jP : P ⋙ E ≅ EA ⋙ p) (jQ : Q ⋙ E ≅ EB ⋙ q)
    {x y : A} {z t : B} {x' y₀ y₁ : A'} {z₀ z₁ t₀ t₁ : B'}
    (r : x ⟶ y) (e : P.obj y ⟶ Q.obj z) (b : z ⟶ t)
    (u : EA.obj x ⟶ x') (d : EA.obj y ⟶ y₀) (v : y₀ ⟶ y₁)
    (w : EB.obj t ⟶ t₀) (k : t₀ ⟶ t₁)
    (j : EB.obj z ⟶ z₀) (v' : z₀ ⟶ z₁) (bb : z₁ ⟶ t₁)
    (rr : x' ⟶ y₁) (e₀ : p.obj y₀ ⟶ q.obj z₀) (e₁ : p.obj y₁ ⟶ q.obj z₁)
    (hb : EB.map b ≫ w ≫ k = j ≫ v' ≫ bb)
    (he : E.map e ≫ jQ.hom.app z ≫ q.map j =
      jP.hom.app y ≫ p.map d ≫ e₀)
    (hn : e₀ ≫ q.map v' = p.map v ≫ e₁)
    (hr : EA.map r ≫ d ≫ v = u ≫ rr) :
    E.map (P.map r ≫ e ≫ Q.map b) ≫ jQ.hom.app t ≫ q.map (w ≫ k) =
      jP.hom.app x ≫ p.map u ≫ p.map rr ≫ e₁ ≫ q.map bb := by
  have hq := jQ.hom.naturality b
  have hp := jP.hom.naturality r
  dsimp only [CategoryTheory.Functor.comp_map] at hq hp
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hq]
  have hb' := congrArg q.map hb
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hb'
  rw [hb']
  rw [reassoc_of% he, reassoc_of% hn, reassoc_of% hp]
  have hr' := congrArg p.map hr
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hr'
  rw [reassoc_of% hr']

private theorem left_route_realization
    {A B C A' B' C' K K' I I' U U' V V' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    [Category* K] [Category* K'] [Category* I] [Category* I']
    [Category* U] [Category* U'] [Category* V] [Category* V']
    (E : C ⥤ C') (EA : A ⥤ A') (EB : B ⥤ B')
    (P : A ⥤ C) (Q : B ⥤ C) (p : A' ⥤ C') (q : B' ⥤ C')
    (jP : P ⋙ E ≅ EA ⋙ p) (jQ : Q ⋙ E ≅ EB ⋙ q)
    (yf : K ⥤ A) (zf : K ⥤ B) (EK : K ⥤ K')
    (yfb : K' ⥤ A') (zfb : K' ⥤ B')
    (ee : yf ⋙ P ⟶ zf ⋙ Q)
    (dd : yf ⋙ EA ≅ EK ⋙ yfb) (jj : zf ⋙ EB ≅ EK ⋙ zfb)
    (ee₀ : yfb ⋙ p ⟶ zfb ⋙ q)
    (rf : I ⥤ U) (aa : I ⥤ V) (T₀ : U ⥤ A) (T₁ : I ⥤ K) (T₃ : V ⥤ B)
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ yf) (b : T₁ ⋙ zf ⟶ aa ⋙ T₃)
    (EU : U ⥤ U') (EI : I ⥤ I') (EV : V ⥤ V')
    (rfb : I' ⥤ U') (aab : I' ⥤ V')
    (S₀ : U' ⥤ A') (S₁ : I' ⥤ K') (S₃ : V' ⥤ B')
    (jr : rf ⋙ EU ≅ EI ⋙ rfb) (ja : aa ⋙ EV ≅ EI ⋙ aab)
    (s₀ : T₀ ⋙ EA ≅ EU ⋙ S₀) (s₁ : T₁ ⋙ EK ≅ EI ⋙ S₁)
    (s₃ : T₃ ⋙ EB ≅ EV ⋙ S₃)
    (rr : rfb ⋙ S₀ ⟶ S₁ ⋙ yfb) (bb : S₁ ⋙ zfb ⟶ aab ⋙ S₃) (J : I)
    (hb : EB.map (b.app J) ≫ s₃.hom.app (aa.obj J) ≫ S₃.map (ja.hom.app J) =
      jj.hom.app (T₁.obj J) ≫ zfb.map (s₁.hom.app J) ≫ bb.app (EI.obj J))
    (he : mateRouteLeft E ee jQ.hom jj.hom (T₁.obj J) =
      mateRouteRight p jP.hom dd.hom ee₀ (T₁.obj J))
    (hr : EA.map (r.app J) ≫ dd.hom.app (T₁.obj J) ≫ yfb.map (s₁.hom.app J) =
      s₀.hom.app (rf.obj J) ≫ S₀.map (jr.hom.app J) ≫ rr.app (EI.obj J))
    (target : E.obj (Q.obj (T₃.obj (aa.obj J))) ⟶
      q.obj (S₃.obj (aab.obj (EI.obj J))))
    (source : E.obj (P.obj (T₀.obj (rf.obj J))) ⟶
      p.obj (S₀.obj (rfb.obj (EI.obj J))))
    (htarget : jQ.hom.app (T₃.obj (aa.obj J)) ≫
      q.map (s₃.hom.app (aa.obj J) ≫ S₃.map (ja.hom.app J)) = target)
    (hsource : jP.hom.app (T₀.obj (rf.obj J)) ≫
      p.map (s₀.hom.app (rf.obj J)) ≫ p.map (S₀.map (jr.hom.app J)) = source) :
    E.map (mateRouteLeft P r ee b J) ≫ target =
      source ≫ mateRouteLeft p rr ee₀ bb (EI.obj J) := by
  have hn := (ee₀.naturality (s₁.hom.app J)).symm
  dsimp only [Functor.comp_map] at hn
  dsimp only [mateRouteLeft, mateRouteRight] at he
  have hh := left_route_algebra E EA EB P Q p q jP jQ (r.app J) (ee.app (T₁.obj J))
    (b.app J) (s₀.hom.app (rf.obj J)) (dd.hom.app (T₁.obj J))
    (yfb.map (s₁.hom.app J)) (s₃.hom.app (aa.obj J)) (S₃.map (ja.hom.app J))
    (jj.hom.app (T₁.obj J)) (zfb.map (s₁.hom.app J)) (bb.app (EI.obj J))
    (S₀.map (jr.hom.app J) ≫ rr.app (EI.obj J))
    (ee₀.app (EK.obj (T₁.obj J))) (ee₀.app (S₁.obj (EI.obj J))) hb he hn hr
  subst target
  subst source
  simpa only [mateRouteLeft, Functor.map_comp, Functor.comp_obj, Category.assoc] using hh

private theorem right_route_algebra
    {C C' A B : Type*} [Category* C] [Category* C'] [Category* A] [Category* B]
    (E : C ⥤ C') (S : A ⥤ C') (q : B ⥤ C')
    {V U X Y : C} {V' U' X' Z' K' H' : A} {W T T' : B}
    {L P : C'}
    (b : V ⟶ U) (e : U ⟶ X) (r : X ⟶ Y)
    (t : E.obj Y ⟶ q.obj W) (w : W ⟶ T) (k : T ⟶ T')
    (sX : E.obj X ⟶ S.obj X') (sU : E.obj U ⟶ S.obj U')
    (e₀ : U' ⟶ X') (z : X' ⟶ Z') (k₀ : Z' ⟶ H')
    (j : U' ⟶ V') (v : V' ⟶ K') (e₁ : K' ⟶ H')
    (r₀ : S.obj Z' ⟶ q.obj T) (r₁ : S.obj H' ⟶ q.obj T')
    (source : E.obj V ⟶ L) (b₀ : L ⟶ S.obj V')
    (v₀ : L ⟶ P) (b₁ : P ⟶ S.obj K')
    (hr : E.map r ≫ t ≫ q.map w = sX ≫ S.map z ≫ r₀)
    (hn : r₀ ≫ q.map k = S.map k₀ ≫ r₁)
    (hs : E.map e ≫ sX = sU ≫ S.map e₀)
    (hb : E.map b ≫ sU ≫ S.map j = source ≫ b₀)
    (he : e₀ ≫ z ≫ k₀ = j ≫ v ≫ e₁)
    (hl : b₀ ≫ S.map v = v₀ ≫ b₁) :
    E.map (b ≫ e ≫ r) ≫ t ≫ q.map (w ≫ k) =
      source ≫ v₀ ≫ b₁ ≫ S.map e₁ ≫ r₁ := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, hn, reassoc_of% hs]
  have he' := congrArg S.map he
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at he'
  rw [reassoc_of% he']
  rw [reassoc_of% hb, reassoc_of% hl]

private theorem right_route_realization
    {GY GX GC GX' SY SX SC SX' HY HC HX' TY TC TX' : Type*}
    [Category* GY] [Category* GX] [Category* GC] [Category* GX']
    [Category* SY] [Category* SX] [Category* SC] [Category* SX']
    [Category* HY] [Category* HC] [Category* HX']
    [Category* TY] [Category* TC] [Category* TX']
    (EY : GY ⥤ SY) (EX : GX ⥤ SX) (EC : GC ⥤ SC) (EX' : GX' ⥤ SX')
    (FY : HY ⥤ TY) (FC : HC ⥤ TC) (FX' : HX' ⥤ TX')
    (lc : GY ⥤ GC) (ff : GX ⥤ GY) (la : GX ⥤ GX') (ff' : GX' ⥤ GC)
    (sc : SY ⥤ SC) (sf : SX ⥤ SY) (sa : SX ⥤ SX') (sf' : SX' ⥤ SC)
    (lcb : HY ⥤ HC) (ffb' : HX' ⥤ HC) (tc : TY ⥤ TC) (tf' : TX' ⥤ TC)
    (DY : GY ⥤ HY) (DC : GC ⥤ HC) (DX' : GX' ⥤ HX')
    (SY' : SY ⥤ TY) (SC' : SC ⥤ TC) (SX'' : SX' ⥤ TX')
    (pc : lc ⋙ EC ≅ EY ⋙ sc) (pf : ff ⋙ EY ≅ EX ⋙ sf)
    (pa : la ⋙ EX' ≅ EX ⋙ sa) (pf' : ff' ⋙ EC ≅ EX' ⋙ sf')
    (pcb : lcb ⋙ FC ≅ FY ⋙ tc) (pfb' : ffb' ⋙ FC ≅ FX' ⋙ tf')
    (jY : DY ⋙ FY ≅ EY ⋙ SY') (jC : DC ⋙ FC ≅ EC ⋙ SC')
    (jX' : DX' ⋙ FX' ≅ EX' ⋙ SX'')
    (ee : ff ⋙ lc ⟶ la ⋙ ff') (se : sf ⋙ sc ⟶ sa ⋙ sf')
    (b : DY ⋙ lcb ⟶ lc ⋙ DC) (r : ff' ⋙ DC ⟶ DX' ⋙ ffb')
    (bs : SY' ⋙ tc ⟶ sc ⋙ SC') (rs : sf' ⋙ SC' ⟶ SX'' ⋙ tf') (J : GX)
    (hr : FC.map (r.app (la.obj J)) ≫ pfb'.hom.app (DX'.obj (la.obj J)) ≫
        tf'.map (jX'.hom.app (la.obj J)) =
      jC.hom.app (ff'.obj (la.obj J)) ≫ SC'.map (pf'.hom.app (la.obj J)) ≫
        rs.app (EX'.obj (la.obj J)))
    (hb : FC.map (b.app (ff.obj J)) ≫ jC.hom.app (lc.obj (ff.obj J)) ≫
        SC'.map (pc.hom.app (ff.obj J)) =
      pcb.hom.app (DY.obj (ff.obj J)) ≫ tc.map (jY.hom.app (ff.obj J)) ≫
        bs.app (EY.obj (ff.obj J)))
    (he : mateRouteLeft EC ee pf'.hom pa.hom J =
      mateRouteRight sc pc.hom pf.hom se J)
    (target : FC.obj (ffb'.obj (DX'.obj (la.obj J))) ⟶
      tf'.obj (SX''.obj (sa.obj (EX.obj J))))
    (source : FC.obj (lcb.obj (DY.obj (ff.obj J))) ⟶
      tc.obj (SY'.obj (sf.obj (EX.obj J))))
    (htarget : pfb'.hom.app (DX'.obj (la.obj J)) ≫
      tf'.map (jX'.hom.app (la.obj J) ≫ SX''.map (pa.hom.app J)) = target)
    (hsource : (pcb.hom.app (DY.obj (ff.obj J)) ≫ tc.map (jY.hom.app (ff.obj J))) ≫
      tc.map (SY'.map (pf.hom.app J)) = source) :
    FC.map (mateRouteRight DC b ee r J) ≫ target =
      source ≫ mateRouteRight SC' bs se rs (EX.obj J) := by
  have hs := jC.hom.naturality (ee.app J)
  have hn := (rs.naturality (pa.hom.app J)).symm
  have hl := (bs.naturality (pf.hom.app J)).symm
  dsimp only [Functor.comp_map] at hs hn hl
  dsimp only [mateRouteLeft, mateRouteRight] at he
  have hh := right_route_algebra FC SC' tf' (b.app (ff.obj J)) (DC.map (ee.app J))
    (r.app (la.obj J)) (pfb'.hom.app (DX'.obj (la.obj J)))
    (jX'.hom.app (la.obj J)) (SX''.map (pa.hom.app J))
    (jC.hom.app (ff'.obj (la.obj J))) (jC.hom.app (lc.obj (ff.obj J)))
    (EC.map (ee.app J)) (pf'.hom.app (la.obj J)) (sf'.map (pa.hom.app J))
    (pc.hom.app (ff.obj J)) (sc.map (pf.hom.app J)) (se.app (EX.obj J))
    (rs.app (EX'.obj (la.obj J))) (rs.app (sa.obj (EX.obj J)))
    (pcb.hom.app (DY.obj (ff.obj J)) ≫ tc.map (jY.hom.app (ff.obj J)))
    (bs.app (EY.obj (ff.obj J))) (tc.map (SY'.map (pf.hom.app J)))
    (bs.app (sf.obj (EX.obj J))) hr hn hs
    (by simpa only [Category.assoc] using hb) he hl
  subst source
  subst target
  simpa only [mateRouteRight, Functor.comp_obj, Category.assoc] using hh

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

attribute [local irreducible] scalarAmbientExchange scalarExchangeLeft scalarExchangeRight
  scalarSectionPushComparison sectionRectangleLambda sectionRectangleRho
  sectionRectangleExchange sectionRectangleSource sectionRectangleTarget
  sectionRectangleLeft sectionRectangleRight

private theorem iso_square_transport
    {A B C D A' B' C' D' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* A'] [Category* B'] [Category* C'] [Category* D']
    {E₀ : A ⥤ A'} {E₁ : B ⥤ B'} {E₂ : C ⥤ C'} {E₃ : D ⥤ D'}
    {f : A ⥤ B} {a : B ⥤ D} {c : A ⥤ C} {g : C ⥤ D} {h : A ⥤ D}
    {fb : A' ⥤ B'} {ab : B' ⥤ D'} {cb : A' ⥤ C'} {gb : C' ⥤ D'} {hb : A' ⥤ D'}
    (jf : f ⋙ E₁ ≅ E₀ ⋙ fb) (ja : a ⋙ E₃ ≅ E₁ ⋙ ab)
    (jc : c ⋙ E₂ ≅ E₀ ⋙ cb) (jg : g ⋙ E₃ ≅ E₂ ⋙ gb)
    (jh : h ⋙ E₃ ≅ E₀ ⋙ hb)
    (x : h ≅ f ⋙ a) (xb : hb ≅ fb ⋙ ab)
    (y : h ≅ c ⋙ g) (yb : hb ≅ cb ⋙ gb)
    (hx : ∀ M, jh.hom.app M ≫ xb.hom.app (E₀.obj M) =
      E₃.map (x.hom.app M) ≫ ja.hom.app (f.obj M) ≫ ab.map (jf.hom.app M))
    (hy : ∀ M, jh.hom.app M ≫ yb.hom.app (E₀.obj M) =
      E₃.map (y.hom.app M) ≫ jg.hom.app (c.obj M) ≫ gb.map (jc.hom.app M))
    (M : A) :
    E₃.map ((y.symm ≪≫ x).hom.app M) ≫ ja.hom.app (f.obj M) ≫
        ab.map (jf.hom.app M) =
      jg.hom.app (c.obj M) ≫ gb.map (jc.hom.app M) ≫
        (yb.symm ≪≫ xb).hom.app (E₀.obj M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [← hx]
  have hh := congrArg (fun t ↦ E₃.map (y.inv.app M) ≫ t ≫
    yb.inv.app (E₀.obj M)) (hy M)
  have hh' : E₃.map (y.inv.app M) ≫ jh.hom.app M =
      jg.hom.app (c.obj M) ≫ gb.map (jc.hom.app M) ≫ yb.inv.app (E₀.obj M) := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
      ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app] at hh
    simpa [Category.assoc] using hh
  rw [reassoc_of% hh']

private theorem iso_square_transport_to
    {A B C D A' B' C' D' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* A'] [Category* B'] [Category* C'] [Category* D']
    {E₀ : A ⥤ A'} {E₁ : B ⥤ B'} {E₂ : C ⥤ C'} {E₃ : D ⥤ D'}
    {f : A ⥤ B} {a : B ⥤ D} {c : A ⥤ C} {g : C ⥤ D} {h : A ⥤ D}
    {fb : A' ⥤ B'} {ab : B' ⥤ D'} {cb : A' ⥤ C'} {gb : C' ⥤ D'} {hb : A' ⥤ D'}
    (jf : f ⋙ E₁ ≅ E₀ ⋙ fb) (ja : a ⋙ E₃ ≅ E₁ ⋙ ab)
    (jc : c ⋙ E₂ ≅ E₀ ⋙ cb) (jg : g ⋙ E₃ ≅ E₂ ⋙ gb)
    (jh : h ⋙ E₃ ≅ E₀ ⋙ hb)
    (x : h ≅ f ⋙ a) (xb : hb ≅ fb ⋙ ab)
    (y : h ≅ c ⋙ g) (yb : hb ≅ cb ⋙ gb)
    (hx : ∀ M, compositionCoherence jf ja jh x xb M)
    (hy : ∀ M, compositionCoherence jc jg jh y yb M)
    (ss : c ⋙ g ≅ f ⋙ a) (tt : cb ⋙ gb ≅ fb ⋙ ab)
    (hs : y.symm ≪≫ x = ss) (ht : yb.symm ≪≫ xb = tt)
    (M : A) :
    squareCoherence jf ja jc jg ss.hom tt.hom M := by
  subst ss
  subst tt
  exact iso_square_transport jf ja jc jg jh x xb y yb hx hy M

private theorem ambient_mate
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    scalarAmbientExchange R sq =
      (mateEquiv (adj R f) (adj R f')
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R sq).hom)).natTrans := by
  unfold scalarAmbientExchange
  rfl

private theorem scalar_rho_mate (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U) :
    rho φ h b = (mateEquiv (adj Λ h) (adj Λ' h)
      (TwoSquare.mk _ _ _ _ b.hom)).natTrans := by
  unfold rho
  rfl

private theorem section_exchange_mate
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    sectionRectangleExchange R sq =
      (mateEquiv (ModuleRingedComparison.derivedAdjunction R f)
        (ModuleRingedComparison.derivedAdjunction R f')
        (TwoSquare.mk _ _ _ _
          ((ModuleRingedComparison.derivedPullbackComposition R f' c).symm ≪≫
            eqToIso (congrArg
              (fun k : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback R k)
              sq.toCommSq.w.symm) ≪≫
            ModuleRingedComparison.derivedPullbackComposition R a f).hom)).natTrans := by
  unfold sectionRectangleExchange
  rfl

private theorem scalar_derived_mate
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    (mateEquiv (adj R h) (ModuleRingedComparison.derivedAdjunction R h)
      (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison R h).inv)).natTrans =
        (scalarSectionPushComparison R h).hom := by
  unfold scalarSectionPushComparison
  rfl

private theorem scalar_pull_comp_section
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (M : DerivedCategory (Modules R W)) :
    compositionCoherence (scalarSectionPullComparison R k)
      (scalarSectionPullComparison R h) (scalarSectionPullComparison R (h ≫ k))
      (scalarPullbackComposition R h k)
      (ModuleRingedComparison.derivedPullbackComposition R h k) M := by
  unfold compositionCoherence
  have hm := ModuleRingedComparison.derivedPullComp R h k M
  unfold ModuleRingedComparison.internalDerivedPullback
    ModuleRingedComparison.comparisonSource at hm
  unfold scalarSectionPullComparison scalarPullbackComposition L
    CondensedRing.moduleObjectDerivedPullback
  exact hm

private theorem exchange_section
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (J : DerivedCategory (Modules R X)) :
    mateRouteLeft (ModuleRingedComparison.derivedFunctor R C)
        (scalarAmbientExchange R sq) (scalarSectionPushComparison R f').hom
        (scalarSectionPullComparison R a).hom J =
      mateRouteRight (ModuleRingedComparison.derivedPullback R c)
        (scalarSectionPullComparison R c).hom (scalarSectionPushComparison R f).hom
        (sectionRectangleExchange R sq) J := by
  apply mate_transport_of_eq
    (E₀ := (ModuleRingedComparison.derivedFunctor R Y))
    (E₁ := (ModuleRingedComparison.derivedFunctor R X))
    (E₂ := (ModuleRingedComparison.derivedFunctor R C))
    (E₃ := (ModuleRingedComparison.derivedFunctor R X'))
    (adj R f) (adj R f')
    (ModuleRingedComparison.derivedAdjunction R f)
    (ModuleRingedComparison.derivedAdjunction R f')
    (scalarSectionPullComparison R f) (scalarSectionPullComparison R f')
    (scalarSectionPushComparison R f) (scalarSectionPushComparison R f')
    ?_ ?_ (scalarSectionPullComparison R c) (scalarSectionPullComparison R a)
    (scalarPullbackSquare R sq).hom _ ?_
    (scalarAmbientExchange R sq) (sectionRectangleExchange R sq)
    (ambient_mate R sq) (section_exchange_mate R sq) J
  · exact scalar_derived_mate R f
  · exact scalar_derived_mate R f'
  · intro M
    have hy : ∀ M : DerivedCategory (Modules R Y),
        compositionCoherence (scalarSectionPullComparison R c)
          (scalarSectionPullComparison R f') (scalarSectionPullComparison R (a ≫ f))
          ((eqToIso (congrArg (fun t : X' ⟶ Y ↦ L R t) sq.toCommSq.w)) ≪≫
            scalarPullbackComposition R f' c)
          ((eqToIso (congrArg (fun t : X' ⟶ Y ↦
            ModuleRingedComparison.derivedPullback R t) sq.toCommSq.w)) ≪≫
              ModuleRingedComparison.derivedPullbackComposition R f' c) M := by
      exact compositionCoherence_eq
        (fun t : X' ⟶ Y ↦ L R t)
        (fun t : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback R t)
        (fun t ↦ scalarSectionPullComparison R t)
        (scalarSectionPullComparison R c) (scalarSectionPullComparison R f')
        sq.toCommSq.w (scalarPullbackComposition R f' c)
        (ModuleRingedComparison.derivedPullbackComposition R f' c)
        (scalar_pull_comp_section R f' c)
    have hd := reverse_compositor
      (fun t : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback R t) sq.toCommSq.w
      (ModuleRingedComparison.derivedPullbackComposition R f' c)
      (ModuleRingedComparison.derivedPullbackComposition R a f)
    let proofSquare := iso_square_transport_to
      (A := DerivedCategory (Modules R Y)) (B := DerivedCategory (Modules R X))
      (C := DerivedCategory (Modules R C)) (D := DerivedCategory (Modules R X'))
      (A' := DerivedCategory (ModuleRingedComparison.modules R Y))
      (B' := DerivedCategory (ModuleRingedComparison.modules R X))
      (C' := DerivedCategory (ModuleRingedComparison.modules R C))
      (D' := DerivedCategory (ModuleRingedComparison.modules R X'))
      (E₀ := (ModuleRingedComparison.derivedFunctor R Y))
      (E₁ := (ModuleRingedComparison.derivedFunctor R X))
      (E₂ := (ModuleRingedComparison.derivedFunctor R C))
      (E₃ := (ModuleRingedComparison.derivedFunctor R X'))
      (f := L R f) (a := L R a) (c := L R c) (g := L R f') (h := L R (a ≫ f))
      (fb := ModuleRingedComparison.derivedPullback R f)
      (ab := ModuleRingedComparison.derivedPullback R a)
      (cb := ModuleRingedComparison.derivedPullback R c)
      (gb := ModuleRingedComparison.derivedPullback R f')
      (hb := ModuleRingedComparison.derivedPullback R (a ≫ f))
      (scalarSectionPullComparison R f) (scalarSectionPullComparison R a)
      (scalarSectionPullComparison R c) (scalarSectionPullComparison R f')
      (scalarSectionPullComparison R (a ≫ f))
      (scalarPullbackComposition R a f)
      (ModuleRingedComparison.derivedPullbackComposition R a f)
      ((eqToIso (congrArg (fun t : X' ⟶ Y ↦ L R t) sq.toCommSq.w)) ≪≫
        (scalarPullbackComposition R f' c))
      ((eqToIso (congrArg (fun t : X' ⟶ Y ↦
        ModuleRingedComparison.derivedPullback R t) sq.toCommSq.w)) ≪≫
          ModuleRingedComparison.derivedPullbackComposition R f' c)
      (scalar_pull_comp_section R a f) hy
      (scalarPullbackSquare R sq)
      ((ModuleRingedComparison.derivedPullbackComposition R f' c).symm ≪≫
        eqToIso (congrArg (fun t : X' ⟶ Y ↦
          ModuleRingedComparison.derivedPullback R t) sq.toCommSq.w.symm) ≪≫
        ModuleRingedComparison.derivedPullbackComposition R a f) (scalarPullbackSquare_eq R sq) hd M
    exact proofSquare

private theorem lambda_section (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) (J : DerivedCategory (Modules Λ V)) :
    (ModuleRingedComparison.derivedEquivalence Λ' U).functor.map (b.hom.app J) ≫
        sU.derived.hom.app ((L Λ h).obj J) ≫
        sU.pair.derived.map ((scalarSectionPullComparison Λ h).hom.app J) =
      (scalarSectionPullComparison Λ' h).hom.app ((D φ V).obj J) ≫
        (ModuleRingedComparison.derivedPullback Λ' h).map (sV.derived.hom.app J) ≫
        (sectionRectangleLambda φ h sU sV b p).hom.app
          ((ModuleRingedComparison.derivedEquivalence Λ V).functor.obj J) := by
  unfold sectionRectangleLambda
  exact (sectionRectangleLambda_witness φ h sU sV b p).choose_spec J

private theorem rho_section (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) (J : DerivedCategory (Modules Λ U)) :
    (ModuleRingedComparison.derivedEquivalence Λ' V).functor.map ((rho φ h b).app J) ≫
        (scalarSectionPushComparison Λ' h).hom.app ((D φ U).obj J) ≫
        (ModuleRingedComparison.derivedPushforward Λ' h).map (sU.derived.hom.app J) =
      sV.derived.hom.app ((F Λ h).obj J) ≫
        sV.pair.derived.map ((scalarSectionPushComparison Λ h).hom.app J) ≫
        (sectionRectangleRho φ h sU sV b p).app
          ((ModuleRingedComparison.derivedEquivalence Λ U).functor.obj J) := by
  unfold rho sectionRectangleRho
  apply mate_transport
    (E₀ := (ModuleRingedComparison.derivedEquivalence Λ V).functor)
    (E₁ := (ModuleRingedComparison.derivedEquivalence Λ U).functor)
    (E₂ := (ModuleRingedComparison.derivedEquivalence Λ' V).functor)
    (E₃ := (ModuleRingedComparison.derivedEquivalence Λ' U).functor)
    (adj Λ h) (adj Λ' h)
    (ModuleRingedComparison.derivedAdjunction Λ h)
    (ModuleRingedComparison.derivedAdjunction Λ' h)
    (scalarSectionPullComparison Λ h) (scalarSectionPullComparison Λ' h)
    (scalarSectionPushComparison Λ h) (scalarSectionPushComparison Λ' h)
    ?_ ?_ sV.derived sU.derived b.hom (sectionRectangleLambda φ h sU sV b p).hom ?_ J
  · exact scalar_derived_mate Λ h
  · exact scalar_derived_mate Λ' h
  · simpa only [sectionRectangleLambda] using
      (sectionRectangleLambda_witness φ h sU sV b p).choose_spec

private theorem left_route_section (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedEquivalence Λ' C).functor.map (scalarExchangeLeft φ sq b J) ≫
        (sectionRectangleTarget φ a f' (s X') J).hom =
      (sectionRectangleSource φ f c (s Y) J).hom ≫ sectionRectangleLeft φ sq b s p J := by
  unfold scalarExchangeLeft sectionRectangleLeft
  apply left_route_realization
    (ModuleRingedComparison.derivedFunctor Λ' C)
    (ModuleRingedComparison.derivedFunctor Λ' Y)
    (ModuleRingedComparison.derivedFunctor Λ' X')
    (L Λ' c) (F Λ' f')
    (ModuleRingedComparison.derivedPullback Λ' c)
    (ModuleRingedComparison.derivedPushforward Λ' f')
    (scalarSectionPullComparison Λ' c) (scalarSectionPushComparison Λ' f')
    (F Λ' f) (L Λ' a) (ModuleRingedComparison.derivedFunctor Λ' X)
    (ModuleRingedComparison.derivedPushforward Λ' f)
    (ModuleRingedComparison.derivedPullback Λ' a)
    (scalarAmbientExchange Λ' sq) (scalarSectionPushComparison Λ' f)
    (scalarSectionPullComparison Λ' a) (sectionRectangleExchange Λ' sq)
    (F Λ f) (L Λ a) (D φ Y) (D φ X) (D φ X')
    (rho φ f (b f)) (b a).hom
    (ModuleRingedComparison.derivedFunctor Λ Y)
    (ModuleRingedComparison.derivedFunctor Λ X)
    (ModuleRingedComparison.derivedFunctor Λ X')
    (ModuleRingedComparison.derivedPushforward Λ f)
    (ModuleRingedComparison.derivedPullback Λ a)
    (s Y).pair.derived (s X).pair.derived (s X').pair.derived
    (scalarSectionPushComparison Λ f) (scalarSectionPullComparison Λ a)
    (s Y).derived (s X).derived (s X').derived
    (sectionRectangleRho φ f (s X) (s Y) (b f) (p f))
    (sectionRectangleLambda φ a (s X') (s X) (b a) (p a)).hom J
    (lambda_section φ a (s X') (s X) (b a) (p a) J)
    (exchange_section Λ' sq ((D φ X).obj J))
    (rho_section φ f (s X) (s Y) (b f) (p f) J)
    (sectionRectangleTarget φ a f' (s X') J).hom
    (sectionRectangleSource φ f c (s Y) J).hom ?_ ?_
  · simp only [sectionRectangleTarget, Iso.trans_hom, Iso.app_hom, Iso.app,
      Functor.mapIso_hom, Functor.map_comp, Functor.comp_obj, Category.assoc,
      ModuleRingedComparison.derivedEquivalence, Functor.asEquivalence]
  · simp only [sectionRectangleSource, Iso.trans_hom, Iso.app_hom, Iso.app,
      Functor.mapIso_hom, Functor.map_comp, Functor.comp_obj, Category.assoc,
      ModuleRingedComparison.derivedEquivalence, Functor.asEquivalence]
private theorem right_route_section (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedFunctor Λ' C).map (scalarExchangeRight φ sq b J) ≫
        (sectionRectangleTarget φ a f' (s X') J).hom =
      (sectionRectangleSource φ f c (s Y) J).hom ≫ sectionRectangleRight φ sq b s p J := by
  unfold scalarExchangeRight sectionRectangleRight
  apply right_route_realization
    (ModuleRingedComparison.derivedFunctor Λ Y) (ModuleRingedComparison.derivedFunctor Λ X)
    (ModuleRingedComparison.derivedFunctor Λ C) (ModuleRingedComparison.derivedFunctor Λ X')
    (ModuleRingedComparison.derivedFunctor Λ' Y) (ModuleRingedComparison.derivedFunctor Λ' C)
    (ModuleRingedComparison.derivedFunctor Λ' X')
    (L Λ c) (F Λ f) (L Λ a) (F Λ f')
    (ModuleRingedComparison.derivedPullback Λ c) (ModuleRingedComparison.derivedPushforward Λ f)
    (ModuleRingedComparison.derivedPullback Λ a) (ModuleRingedComparison.derivedPushforward Λ f')
    (L Λ' c) (F Λ' f')
    (ModuleRingedComparison.derivedPullback Λ' c) (ModuleRingedComparison.derivedPushforward Λ' f')
    (D φ Y) (D φ C) (D φ X')
    (s Y).pair.derived (s C).pair.derived (s X').pair.derived
    (scalarSectionPullComparison Λ c) (scalarSectionPushComparison Λ f)
    (scalarSectionPullComparison Λ a) (scalarSectionPushComparison Λ f')
    (scalarSectionPullComparison Λ' c) (scalarSectionPushComparison Λ' f')
    (s Y).derived (s C).derived (s X').derived
    (scalarAmbientExchange Λ sq) (sectionRectangleExchange Λ sq)
    (b c).hom (rho φ f' (b f'))
    (sectionRectangleLambda φ c (s C) (s Y) (b c) (p c)).hom
    (sectionRectangleRho φ f' (s X') (s C) (b f') (p f')) J
    (rho_section φ f' (s X') (s C) (b f') (p f') ((L Λ a).obj J))
    (lambda_section φ c (s C) (s Y) (b c) (p c) ((F Λ f).obj J))
    (exchange_section Λ sq J)
    (sectionRectangleTarget φ a f' (s X') J).hom
    (sectionRectangleSource φ f c (s Y) J).hom ?_ ?_
  · simp only [sectionRectangleTarget, Iso.trans_hom, Iso.app_hom, Iso.app,
      Functor.mapIso_hom, Functor.map_comp, Functor.comp_obj, Category.assoc,
      ModuleRingedComparison.derivedEquivalence, Functor.asEquivalence]
  · simp only [sectionRectangleSource, Iso.trans_hom, Iso.app_hom, Iso.app,
      Functor.mapIso_hom, Functor.map_comp, Functor.comp_obj, Category.assoc,
      ModuleRingedComparison.derivedEquivalence, Functor.asEquivalence]
attribute [local irreducible] rho SectionPullNormalized SectionScalarNormalized

/-- Scalar change commutes with the actual ambient geometric exchange. The second
conjunct supplies normalized section scalar and pullback comparisons, identifies
each realized route with its section route after conjugating by the fixed source
and target comparisons, and asserts equality of the actual section routes. Their
rho and exchange are mates under the independently specified section adjunctions. -/
theorem scalar_geometric_exchange_rectangle (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (normalized : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized φ h (b h))
    (J : DerivedCategory (Modules Λ X)) :
    scalarExchangeLeft φ sq b J = scalarExchangeRight φ sq b J ∧
      ∃ s : ∀ T : Scheme.{u}, SectionScalarComparison φ T,
        (∀ T : Scheme.{u}, SectionScalarNormalized φ T (s T)) ∧
        ∃ p : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
          SectionPullNormalized φ h (s U) (s V) (b h),
          ((sectionRectangleSource φ f c (s Y) J).inv ≫
              (ModuleRingedComparison.derivedFunctor Λ' C).map (scalarExchangeLeft φ sq b J) ≫
              (sectionRectangleTarget φ a f' (s X') J).hom =
            sectionRectangleLeft φ sq b s p J) ∧
          ((sectionRectangleSource φ f c (s Y) J).inv ≫
              (ModuleRingedComparison.derivedFunctor Λ' C).map (scalarExchangeRight φ sq b J) ≫
              (sectionRectangleTarget φ a f' (s X') J).hom =
            sectionRectangleRight φ sq b s p J) ∧
          sectionRectangleLeft φ sq b s p J = sectionRectangleRight φ sq b s p J := by
  have hi : scalarExchangeLeft φ sq b J = scalarExchangeRight φ sq b J := by
    unfold scalarExchangeLeft scalarExchangeRight
    exact mate_rectangle_of_eq
      (T₀ := D φ Y) (T₁ := D φ X) (T₂ := D φ C) (T₃ := D φ X')
      (a := L Λ a) (c := L Λ c) (ab := L Λ' a) (cb := L Λ' c)
      (adj Λ f) (adj Λ f') (adj Λ' f) (adj Λ' f')
      (b f).hom (b f').hom (b a).hom (b c).hom
      (scalarPullbackSquare Λ sq).hom (scalarPullbackSquare Λ' sq).hom
      (scalar_pullback_square_coherence φ sq b normalized)
      (rho φ f (b f)) (rho φ f' (b f'))
      (scalarAmbientExchange Λ sq) (scalarAmbientExchange Λ' sq)
      (scalar_rho_mate φ f (b f)) (scalar_rho_mate φ f' (b f'))
      (ambient_mate Λ sq) (ambient_mate Λ' sq) J
  have hf := normalized_scalar_section_family φ b normalized
  rcases hf with ⟨s, hs, p⟩
  have hl := left_route_section φ sq b s p J
  have hr := right_route_section φ sq b s p J
  have hl' : (sectionRectangleSource φ f c (s Y) J).inv ≫
      (ModuleRingedComparison.derivedFunctor Λ' C).map (scalarExchangeLeft φ sq b J) ≫
      (sectionRectangleTarget φ a f' (s X') J).hom =
      sectionRectangleLeft φ sq b s p J := by
    exact conjugate_route _ _ _ _ hl
  have hr' : (sectionRectangleSource φ f c (s Y) J).inv ≫
      (ModuleRingedComparison.derivedFunctor Λ' C).map (scalarExchangeRight φ sq b J) ≫
      (sectionRectangleTarget φ a f' (s X') J).hom =
      sectionRectangleRight φ sq b s p J := by
    exact conjugate_route _ _ _ _ hr
  refine ⟨hi, s, hs, p, hl', hr', ?_⟩
  exact hl'.symm.trans ((congrArg (fun k ↦
    (sectionRectangleSource φ f c (s Y) J).inv ≫
      (ModuleRingedComparison.derivedFunctor Λ' C).map k ≫
      (sectionRectangleTarget φ a f' (s X') J).hom) hi).trans hr')

end AlgebraicGeometry.ProEtale.QuotientChange
