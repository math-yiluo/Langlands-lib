/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.OverlapSingleChartRestriction
import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent

/-! # Restricting a conjugated transition to an iterated overlap

Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-conjugate-restriction). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry
noncomputable section
set_option allowUnsafeReducibility true
attribute [local reducible] Precoverage.ZeroHypercover.pullback₁
  Scheme.Cover.pullbackHom
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The comparison of tensor and abstract inverse image determined by their adjunctions.
Source: Stacks Project, Tag 0096.
(blueprint: lem-pc-overlap-conjugate-restriction). 
(blueprint: lem-pc-overlap-conjugate-restriction-explicit)
-/
@[irreducible]
def overlapAdjunctionComparison {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
  Adjunction.leftAdjointUniq
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction p)

/-- The direct model comparison with prescribed chart projections.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: lem-pc-overlap-conjugate-restriction). 
(blueprint: lem-pc-overlap-conjugate-restriction-explicit)
-/
@[irreducible]
def overlapDirectModelComparison {H H₀ A B : Scheme.{u}}
    (t : H ⟶ H₀) (r : H₀ ⟶ A) (k : H ⟶ A)
    (v : H ⟶ B) (u : B ⟶ A) (htr : t ≫ r = k) (hvu : v ≫ u = k)
    (N : A.Modules) :
    (Scheme.Modules.tensorPullback t).obj ((Scheme.Modules.pullback r).obj N) ≅
      (Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback u).obj N) :=
  (overlapAdjunctionComparison t).app _ ≪≫
    pullbackCompOfEq t r k htr N ≪≫ (pullbackCompOfEq v u k hvu N).symm

/-- The stage model comparison with prescribed chart projections.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: lem-pc-overlap-conjugate-restriction). 
(blueprint: lem-pc-overlap-conjugate-restriction-explicit)
-/
@[irreducible]
def overlapStageModelComparison {K H H₀ A B : Scheme.{u}}
    (d : K ⟶ H) (q : H ⟶ H₀) (r : H₀ ⟶ A)
    (s : K ⟶ B) (u : B ⟶ A) (h : (d ≫ q) ≫ r = s ≫ u) (N : A.Modules) :
    (Scheme.Modules.pullback d).obj
        ((Scheme.Modules.tensorPullback q).obj ((Scheme.Modules.pullback r).obj N)) ≅
      (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback u).obj N) :=
  (Scheme.Modules.pullback d).mapIso ((overlapAdjunctionComparison q).app _) ≪≫
    (Scheme.Modules.pullbackComp d q).app _ ≪≫
    pullbackCompOfEq (d ≫ q) r (s ≫ u) h N ≪≫
    ((Scheme.Modules.pullbackComp s u).app N).symm

/-- The part of the iterated comparison preceding the component isomorphism.
Source: Stacks Project, Tag 0095.
(blueprint: lem-pc-overlap-conjugate-restriction). 
(blueprint: lem-pc-overlap-conjugate-restriction-explicit)
-/
def overlapIteratedRestrictionIso {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀) :
    (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapIteratedChartHom U q p t h d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) :=
  (Scheme.Modules.pullbackComp _ _).app (N d) ≪≫
    (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _).symm).app (N d) ≪≫
    ((Scheme.Modules.pullbackComp _ _).app (N d)).symm

/-- Comparison from a model restriction to the iterated chart restriction.
Source: Stacks Project, Tag 0095, composition of inverse images.
(blueprint: lem-pc-overlap-conjugate-restriction). 
(blueprint: lem-pc-overlap-conjugate-restriction-explicit)
-/
def overlapDirectRestrictionIso {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (a b d : U.I₀)
    (hd : H ⟶ (U.pullback₁ t).X d)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (r : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ ((U.pullback₁ q).pullback₁ p).X d)
    (hz : z ≫ hd = r ≫ overlapIteratedChartHom U q p t h d)
    (S : H.Modules)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))) :
    (Scheme.Modules.pullback z).obj S ≅
      (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
          ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d))) :=
  (Scheme.Modules.pullback z).mapIso τ ≪≫
    pullbackCompOfEq z hd (r ≫ overlapIteratedChartHom U q p t h d) hz
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) ≪≫
    ((Scheme.Modules.pullbackComp r (overlapIteratedChartHom U q p t h d)).app _).symm ≪≫
    (Scheme.Modules.pullback r).mapIso (overlapIteratedRestrictionIso U q p t h N d).symm

/-- The explicit conjugation of a transition on a direct model overlap.
Source: Stacks Project, Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-conjugate-restriction). 
(blueprint: lem-pc-overlap-conjugate-restriction-explicit)
-/
@[irreducible]
def overlapConjugatedTransition {X Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (t : Z ⟶ X) (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) : S ⟶ T :=
  let D := (modulesPseudofunctor.toDescentData (U.pullback₁ t).f).obj M
  τa.hom ≫ (Scheme.Modules.pullback ha).map (e a).hom ≫
    D.hom ν ha hb hνa hνb ≫ (Scheme.Modules.pullback hb).map (e b).inv ≫ τb.inv


attribute [local implicit_reducible] Precoverage.ZeroHypercover.pullback₁
  PreZeroHypercover.pullback₁ Scheme.Modules.pseudofunctor
  CategoryTheory.Pseudofunctor.comp CategoryTheory.PrelaxFunctor.comp
  CategoryTheory.Bicategory.Adj.forget₁ CategoryTheory.LocallyDiscrete.mkPseudofunctor
  CategoryTheory.PrelaxFunctorStruct.comp Prefunctor.comp
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete CategoryTheory.Cat.of
  CategoryTheory.Bundled.of CategoryTheory.Adjunction.toCat
  CategoryTheory.Pseudofunctor.toDescentData CategoryTheory.Pseudofunctor.DescentData.ofObj
  Quiver.Hom.toLoc

attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.pullbackComp pullbackCompOfEq Scheme.Modules.pullbackCongr
  overlapDirectRestrictionIso overlapIteratedComparison overlapIteratedRestrictionIso
  CategoryTheory.Pseudofunctor.overlapPairBaseChangeHom
  overlapPairSquare CategoryTheory.Pseudofunctor.overlapPairBaseChangeSquare

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true



private theorem conjugate_square {C : Type*} [Category* C]
    {S T A B P Q L R : C} (ξa : S ≅ A) (ξb : T ≅ B)
    (εa : A ≅ P) (εb : B ≅ Q) (ca : P ≅ R) (cb : Q ≅ R)
    (αa : S ≅ L) (αb : T ≅ L) (c : L ≅ R)
    (ha : ξa ≪≫ εa ≪≫ ca = αa ≪≫ c)
    (hb : ξb ≪≫ εb ≪≫ cb = αb ≪≫ c) :
    εa.hom ≫ ca.hom ≫ cb.inv = ξa.inv ≫ αa.hom ≫ αb.inv ≫ ξb.hom ≫ εb.hom := by
  apply (cancel_epi ξa.hom).mp
  apply (cancel_mono cb.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ha' := congrArg Iso.hom ha
  have hb' := congrArg Iso.hom hb
  simp only [Iso.trans_hom] at ha' hb'
  rw [hb']
  simp only [Iso.inv_hom_id_assoc]
  exact ha'

private theorem canonical_square {K H Z : Scheme.{u}} (W : Z.OpenCover.{u})
    (a b : W.I₀) (ra : K ⟶ W.X a) (rb : K ⟶ W.X b) (k : K ⟶ Z)
    (hra : ra ≫ W.f a = k) (hrb : rb ≫ W.f b = k)
    (z : K ⟶ H) (ν : H ⟶ Z) (hzk : z ≫ ν = k) (M : Z.Modules)
    (Ba : (W.X a).Modules) (Bb : (W.X b).Modules) (S T : H.Modules)
    (ξa : (Scheme.Modules.pullback z).obj S ≅ (Scheme.Modules.pullback ra).obj Ba)
    (ξb : (Scheme.Modules.pullback z).obj T ≅ (Scheme.Modules.pullback rb).obj Bb)
    (εa : Ba ≅ (Scheme.Modules.pullback (W.f a)).obj M)
    (εb : Bb ≅ (Scheme.Modules.pullback (W.f b)).obj M)
    (αa : S ≅ (Scheme.Modules.pullback ν).obj M)
    (αb : T ≅ (Scheme.Modules.pullback ν).obj M)
    (hca : ξa.hom ≫ (Scheme.Modules.pullback ra).map εa.hom ≫
        (pullbackCompOfEq ra (W.f a) k hra M).hom =
      (Scheme.Modules.pullback z).map αa.hom ≫ (pullbackCompOfEq z ν k hzk M).hom)
    (hcb : ξb.hom ≫ (Scheme.Modules.pullback rb).map εb.hom ≫
        (pullbackCompOfEq rb (W.f b) k hrb M).hom =
      (Scheme.Modules.pullback z).map αb.hom ≫ (pullbackCompOfEq z ν k hzk M).hom)
    (θ : S ⟶ T) (hθ : θ = αa.hom ≫ αb.inv)
    (β : (Scheme.Modules.pullback ra).obj Ba ⟶ (Scheme.Modules.pullback rb).obj Bb)
    (hβ : β = ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom) :
    (Scheme.Modules.pullback ra).map εa.hom ≫
        (pullbackCompOfEq ra (W.f a) k hra M).hom ≫
        (pullbackCompOfEq rb (W.f b) k hrb M).inv =
      β ≫ (Scheme.Modules.pullback rb).map εb.hom := by
  rw [hβ, hθ, Functor.map_comp]
  exact conjugate_square ξa ξb ((Scheme.Modules.pullback ra).mapIso εa)
    ((Scheme.Modules.pullback rb).mapIso εb)
    (pullbackCompOfEq ra (W.f a) k hra M) (pullbackCompOfEq rb (W.f b) k hrb M)
    ((Scheme.Modules.pullback z).mapIso αa) ((Scheme.Modules.pullback z).mapIso αb)
    (pullbackCompOfEq z ν k hzk M)
    (by apply Iso.ext; simpa only [Iso.trans_hom, Functor.mapIso_hom] using hca)
    (by apply Iso.ext; simpa only [Iso.trans_hom, Functor.mapIso_hom] using hcb)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restriction_square_calc {K X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (z : K ⟶ H)
    (ra : K ⟶ ((U.pullback₁ q).pullback₁ p).X a)
    (rb : K ⟶ ((U.pullback₁ q).pullback₁ p).X b) (k : K ⟶ Z)
    (hra : ra ≫ ((U.pullback₁ q).pullback₁ p).f a = k)
    (hrb : rb ≫ ((U.pullback₁ q).pullback₁ p).f b = k)
    (hza : z ≫ ha = ra ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = rb ≫ overlapIteratedChartHom U q p t h b)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b)))
    (θ : S ⟶ T)
    (hθ : θ = overlapConjugatedTransition U t N M e a b ν ha hb hνa hνb S T τa τb)
    (β : (Scheme.Modules.pullback ra).obj
        ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)).obj
          ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))) ⟶
      (Scheme.Modules.pullback rb).obj
        ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)).obj
          ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))))
    (hβ : β = (overlapRestrictionIso (overlapIteratedChartHom U q p t h a) z ha ra hza
        ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)) _ S
        (overlapCanonicalChartComparison U q p t h N a) τa).inv ≫
      (Scheme.Modules.pullback z).map θ ≫
      (overlapRestrictionIso (overlapIteratedChartHom U q p t h b) z hb rb hzb
        ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b)) _ T
        (overlapCanonicalChartComparison U q p t h N b) τb).hom) :
    (Scheme.Modules.pullback ra).map (overlapIteratedComparison U q p t h N M e a).hom ≫
      (pullbackCompOfEq ra (((U.pullback₁ q).pullback₁ p).f a) k hra M).hom ≫
      (pullbackCompOfEq rb (((U.pullback₁ q).pullback₁ p).f b) k hrb M).inv =
    β ≫ (Scheme.Modules.pullback rb).map
      (overlapIteratedComparison U q p t h N M e b).hom := by
  let V : Y.OpenCover.{u} := U.pullback₁ q
  let W : Z.OpenCover.{u} := V.pullback₁ p
  let ε := overlapIteratedComparison U q p t h N M e
  let ξa := overlapRestrictionIso (overlapIteratedChartHom U q p t h a) z ha ra hza
    ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)) _ S
    (overlapCanonicalChartComparison U q p t h N a) τa
  let ξb := overlapRestrictionIso (overlapIteratedChartHom U q p t h b) z hb rb hzb
    ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b)) _ T
    (overlapCanonicalChartComparison U q p t h N b) τb
  let αa := τa ≪≫ (Scheme.Modules.pullback ha).mapIso (e a) ≪≫
    pullbackCompOfEq ha ((U.pullback₁ t).f a) ν hνa M
  let αb := τb ≪≫ (Scheme.Modules.pullback hb).mapIso (e b) ≪≫
    pullbackCompOfEq hb ((U.pullback₁ t).f b) ν hνb M
  have hzk : z ≫ ν = k := by
    rw [← hνa, ← Category.assoc, hza, Category.assoc]
    have hd : overlapIteratedChartHom U q p t h a ≫ (U.pullback₁ t).f a =
        ((U.pullback₁ q).pullback₁ p).f a := pullback.lift_fst _ _ _
    rw [hd]
    exact hra
  have hca := overlap_single_chart_restriction U q p t h N M e a ν ha hνa
    ra z k hra hza hzk S τa
  have hcb := overlap_single_chart_restriction U q p t h N M e b ν hb hνb
    rb z k hrb hzb hzk T τb
  have hθ' : θ = αa.hom ≫ αb.inv := by
    simpa only [αa, αb, overlapConjugatedTransition,
      modulesPseudofunctor_toDescentData_obj_hom, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using hθ
  apply canonical_square W a b ra rb k hra hrb z ν hzk M
    ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)))
    ((Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b)))
    S T ξa ξb (ε a) (ε b) αa αb _ _ θ hθ' β hβ
  · simpa only [ξa, ε, αa, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hca
  · simpa only [ξb, ε, αb, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hcb



private theorem refl_app_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (M : C) : (Iso.refl F).app M = Iso.refl (F.obj M) := rfl

private theorem compOfEq_refl {K W B : Scheme.{u}}
    (r : K ⟶ W) (d : W ⟶ B) (A : B.Modules) :
    pullbackCompOfEq r d (r ≫ d) rfl A = (Scheme.Modules.pullbackComp r d).app A := by
  simp only [pullbackCompOfEq, Scheme.Modules.pullbackCongr, eqToIso_refl,
    refl_app_eq, Iso.trans_refl]

private theorem chart_comparison_eq {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀) :
    overlapIteratedRestrictionIso U q p t h N d =
      overlapCanonicalChartComparison U q p t h N d := by
  simp only [overlapIteratedRestrictionIso, overlapCanonicalChartComparison,
    overlapIteratedChartHom, Scheme.Cover.pullbackHom]

private theorem direct_restriction_eq {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (a b d : U.I₀)
    (hd : H ⟶ (U.pullback₁ t).X d)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (r : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ ((U.pullback₁ q).pullback₁ p).X d)
    (hz : z ≫ hd = r ≫ overlapIteratedChartHom U q p t h d)
    (S : H.Modules)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))) :
    overlapDirectRestrictionIso U q p t h N a b d hd z r hz S τ =
      overlapRestrictionIso (overlapIteratedChartHom U q p t h d) z hd r hz
        ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) _ S
        (overlapCanonicalChartComparison U q p t h N d) τ := by
  simp only [overlapDirectRestrictionIso, overlapRestrictionIso,
    compOfEq_refl, chart_comparison_eq]


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


private theorem modules_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (g : M ⟶ N) :
    (modulesPseudofunctor.map f.op.toLoc).toFunctor.map g =
      (Scheme.Modules.pullback f).map g := rfl

private theorem pair_square_native
    {ι : Type u} {X Y : Scheme.{u}} {V W : ι → Scheme.{u}}
    (f : ∀ a, V a ⟶ X) (g : ∀ a, W a ⟶ Y) (p : Y ⟶ X)
    (v : ∀ a, W a ⟶ V a) (w : ∀ a, v a ≫ f a = g a ≫ p)
    (A : ∀ a, (V a).Modules) (M : Y.Modules)
    (ε : ∀ a, (Scheme.Modules.pullback (v a)).obj (A a) ≅
      (Scheme.Modules.pullback (g a)).obj M) (a b : ι)
    (φ : (modulesPseudofunctor.map (pullback.fst (f a) (f b)).op.toLoc).toFunctor.obj
        (A a) ⟶
      (modulesPseudofunctor.map (pullback.snd (f a) (f b)).op.toLoc).toFunctor.obj (A b))
    (γ : (modulesPseudofunctor.map (pullback.fst (g a) (g b)).op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map (v a).op.toLoc).toFunctor.obj (A a)) ⟶
      (modulesPseudofunctor.map (pullback.snd (g a) (g b)).op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map (v b).op.toLoc).toFunctor.obj (A b)))
    (hn : ∀ β, β = γ →
      (Scheme.Modules.pullback (pullback.fst (g a) (g b))).map (ε a).hom ≫
        (pullbackCompOfEq (pullback.fst (g a) (g b)) (g a)
          (pullback.fst (g a) (g b) ≫ g a) rfl M).hom ≫
        (pullbackCompOfEq (pullback.snd (g a) (g b)) (g b)
          (pullback.fst (g a) (g b) ≫ g a) pullback.condition.symm M).inv =
      β ≫ (Scheme.Modules.pullback (pullback.snd (g a) (g b))).map (ε b).hom)
    (hφ : modulesPseudofunctor.overlapPairBaseChangeHom
      (f a) (f b) p (v a) (v b) (g a) (g b) (w a) (w b) (A a) (A b) φ = γ) :
    modulesPseudofunctor.overlapPairBaseChangeSquare f g p v w A
      ((modulesPseudofunctor.toDescentData g).obj M) ε a b φ := by
  unfold CategoryTheory.Pseudofunctor.overlapPairBaseChangeSquare
  dsimp only
  rw [modules_map_eq, modules_map_eq, modulesPseudofunctor_toDescentData_obj_hom]
  simpa only [Category.assoc] using hn _ hφ

/-- Explicit-transition intermediate for the conjugated restriction theorem.
A pair morphism whose base change is this restricted conjugate satisfies the pair square.
There is no tensor stage morphism or recovery hypothesis in this statement.
Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-conjugate-restriction-explicit).

Proof: Substitute the equation naming the conjugated transition. Expand the two
direct restriction isomorphisms. Naturality moves the
pullbacks of the component maps through the composition comparisons. Cancel
τ_a and τ_b against their inverses. The naturality equation of the descent datum
on the direct cover identifies the pulled-back transition along z with the
transition on the maps r_a followed by the iterated chart map and r_b followed
by that map. The composition pentagon then identifies its two exterior
comparisons with the comparisons for the descent datum of M on the iterated
cover. The source comparison becomes the hom of overlapIteratedComparison;
the inverse target comparison cancels its hom. Substitute the given base-change
identity and use associativity to obtain overlapPairSquare. Projection equations hz_a,
hz_b and hν give exactly the prescribed base and chart maps. This argument
uses only naturality and invertible comparisons, and also applies to empty
overlaps, repeated charts, zero modules, and identity base changes. -/
theorem overlap_conjugate_restriction_explicit {X Y Z H : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (a b : U.I₀) (ν : H ⟶ Z)
    (ha : H ⟶ (U.pullback₁ t).X a) (hb : H ⟶ (U.pullback₁ t).X b)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν) (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ H)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (S T : H.Modules)
    (τa : S ≅ (Scheme.Modules.pullback ha).obj
      ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
    (τb : T ≅ (Scheme.Modules.pullback hb).obj
      ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b))) (θ : S ⟶ T)
    (hθ : θ = overlapConjugatedTransition U t N M e a b ν ha hb hνa hνb S T τa τb) :
    let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
      (pullback.fst _ _) hza S τa
    let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
      (pullback.snd _ _) hzb T τb
    let W := (U.pullback₁ q).pullback₁ p
    let D := (modulesPseudofunctor.toDescentData W.f).obj M
    let ε := overlapIteratedComparison U q p t h N M e
    let V : Y.OpenCover.{u} := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    ∀ (φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b)),
      modulesPseudofunctor.overlapPairBaseChangeHom (V.f a) (V.f b) p
        (V.pullbackHom p a) (V.pullbackHom p b) (W.f a) (W.f b)
        (V.pullbackHom_map p a) (V.pullbackHom_map p b) (A a) (A b) φ =
        ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom →
      overlapPairSquare V A p D ε a b φ := by
  dsimp only
  intro φ hφ
  unfold overlapPairSquare
  apply pair_square_native (U.pullback₁ q).f (((U.pullback₁ q).pullback₁ p).f) p
    (fun d ↦ Scheme.Cover.pullbackHom (U.pullback₁ q) p d)
    (fun d ↦ Scheme.Cover.pullbackHom_map (U.pullback₁ q) p d)
    (fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) M
    (overlapIteratedComparison U q p t h N M e) a b φ _ _ hφ
  intro β hβ
  apply restriction_square_calc U q p t h N M e a b ν ha hb hνa hνb z
    (pullback.fst _ _) (pullback.snd _ _) _ rfl pullback.condition.symm
    hza hzb S T τa τb θ hθ β
  simpa only [direct_restriction_eq] using hβ

end
end AlgebraicGeometry
