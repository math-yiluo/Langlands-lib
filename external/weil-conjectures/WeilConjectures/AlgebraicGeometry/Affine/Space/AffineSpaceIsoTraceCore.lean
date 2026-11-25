/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceGeometricTopAction
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-! # Identity of the arbitrary affine-space trace action -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

private lemma iso_diagram {C : Type*} [Category C]
    {O U V W P Q T R : C}
    (a : O ≅ U) (b : U ≅ V) (c : O ≅ W) (d : W ≅ V)
    (e : U ≅ P) (f : O ≅ Q) (g : Q ≅ P) (h : O ≅ T) (i : T ≅ R) (j : W ≅ R)
    (h1 : a.hom ≫ b.hom = c.hom ≫ d.hom)
    (h2 : a.hom ≫ e.hom = f.hom ≫ g.hom)
    (h3 : h.hom ≫ i.hom = c.hom ≫ j.hom) :
    b.inv ≫ e.hom ≫ g.inv = d.inv ≫ j.hom ≫ i.inv ≫ h.inv ≫ f.hom := by
  apply (cancel_epi (a.hom ≫ b.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h2, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% h1, Iso.hom_inv_id_assoc, ← reassoc_of% h3]
  simp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem descended_coefficient_square
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (v : X' ⟶ X) (g : Y' ⟶ Y)
    (a : X ⟶ X) (a' : X' ⟶ X')
    (hs : v ≫ p = p' ≫ g) (ha : a ≫ p = p) (ha' : a' ≫ p' = p')
    (hw : a' ≫ v = v ≫ a) (L : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hs)).inv.app L) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' p' p' ha'.symm).inv.app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj L) =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hw)).inv.app
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p p ha.symm).inv.app L) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hs)).inv.app L := by
  have hd : v ≫ p = (a' ≫ v) ≫ p := by rw [hw, Category.assoc, ha]
  have A1 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    a' v p (a' ≫ v) (v ≫ p) (v ≫ p) rfl rfl hd L
  have A2 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    a' p' g p' (v ≫ p) (v ≫ p) ha'.symm hs hs L
  have A3 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    v a p (a' ≫ v) p (v ≫ p) hw ha.symm hd L
  have h := iso_diagram
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' (v ≫ p) (v ≫ p)
      (by rw [← Category.assoc, hw, Category.assoc, ha])).app L)
    ((upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).app L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (a' ≫ v) p (v ≫ p) hd).app L)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' v).app
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj L))
    ((upperStar (ModuleCat.{u + 1} A) a').leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' g (v ≫ p) hs).app L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' g (v ≫ p) hs).app L)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' p' p' ha'.symm).app
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).app L)
    ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p p ha.symm).app L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v a (a' ≫ v) hw).app
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj L)) A1 A2 A3
  simpa only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using h

attribute [local semireducible] affineLinearBaseCoefficient in
private def baseCoefficientPullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y d) ≅
      affineLinearBaseCoefficient A N hA X d :=
  Nat.rec (motive := fun e ↦
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y e) ≅
      affineLinearBaseCoefficient A N hA X e)
    (ordinaryFiniteUnitPullback A f)
    (fun e r ↦ ordinaryFiniteTensorPullback A f (affineLinearBaseCoefficient A N hA Y e)
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≪≫
      ordinaryFiniteTensorRightMapIso A X r
        (ordinaryFiniteShiftedLinePullback A N hA t f hY)) d

private def coefficientBaseChange
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S' d).obj (ordinaryFiniteUnit A S') :=
  (ordinaryFinitePullback A (affineTraceMap f d)).mapIso
      (affineLinearCoefficientDescent A N hA t S hS d) ≪≫
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (affineTraceMap_isPullback f d).toCommSq).app
        (affineLinearBaseCoefficient A N hA S d)).symm ≪≫
    (ordinaryFinitePullback A (affineTraceProjection S' d)).mapIso
      (baseCoefficientPullback A N hA t f hS d) ≪≫
    (affineLinearCoefficientDescent A N hA t S' hS' d).symm

attribute [local irreducible] baseCoefficientPullback coefficientBaseChange

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem coefficientBaseChange_equivariant
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (a' : affineTraceTower S' d ⟶ affineTraceTower S' d)
    (ha : a ≫ affineTraceProjection S d = affineTraceProjection S d)
    (ha' : a' ≫ affineTraceProjection S' d = affineTraceProjection S' d)
    (hw : a' ≫ affineTraceMap f d = affineTraceMap f d ≫ a) :
    (ordinaryFinitePullback A a').map (coefficientBaseChange A N hA t f hS hS' d).hom ≫
        (affineLinearCoefficientPullback A N hA t S' hS' d a' ha').hom =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hw)).inv.app _ ≫
        (ordinaryFinitePullback A (affineTraceMap f d)).map
          (affineLinearCoefficientPullback A N hA t S hS d a ha).hom ≫
        (coefficientBaseChange A N hA t f hS hS' d).hom := by
  have hr := descended_coefficient_square A
    (affineTraceProjection S d) (affineTraceProjection S' d)
    (affineTraceMap f d) f a a' (affineTraceMap_isPullback f d).w ha ha' hw
    (affineLinearBaseCoefficient A N hA S d)
  apply (cancel_mono (affineLinearCoefficientDescent A N hA t S' hS' d).hom).mp
  simp only [coefficientBaseChange, affineLinearCoefficientPullback,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc,
    Iso.inv_hom_id]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a'
    (affineTraceProjection S' d) (affineTraceProjection S' d) ha'.symm).inv.naturality
      (baseCoefficientPullback A N hA t f hS d).hom
  simp only [Functor.comp_map] at hn
  dsimp only [ordinaryFinitePullback] at hr hn ⊢
  rw [hn, reassoc_of% hr]
  have hsquare := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
    (CommSq.mk hw)).inv.naturality
      (affineLinearCoefficientDescent A N hA t S hS d).hom
  simp only [Functor.comp_map] at hsquare
  erw [reassoc_of% hsquare]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem action_baseChange
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (a' : affineTraceTower S' d ⟶ affineTraceTower S' d)
    (sa : IsPullback a (affineTraceProjection S d) (affineTraceProjection S d) (𝟙 S))
    (sa' : IsPullback a' (affineTraceProjection S' d) (affineTraceProjection S' d) (𝟙 S'))
    (hw : a' ≫ affineTraceMap f d = affineTraceMap f d ≫ a) :
    ∃ C : (ordinaryFinitePullback A f).obj
        ((affineTraceLeft A S d).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ≅
        (affineTraceLeft A S' d).obj
          ((affineTraceRight A N hA S' d).obj (ordinaryFiniteUnit A S')),
      (ordinaryFinitePullback A f).map (affineLinearTraceAction N hN A hA t S hS d a sa) ≫
          C.hom =
        C.hom ≫ affineLinearTraceAction N hN A hA t S' hS' d a' sa' := by
  let := affineTraceNoetherian S d
  let := affineTraceNoetherian S' d
  let sq := affineTraceMap_isPullback f d
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let B := (asIso (rightDerivedLowerShriekBaseChangeMap A sq)).app
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
  let C := (ordinaryFinitePullback A f).mapIso
      (affineLinearCompactComparison N hN A hA S hS d) ≪≫ B ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S' d)).mapIso (coefficientBaseChange A N hA t f hS hS' d) ≪≫
    (affineLinearCompactComparison N hN A hA S' hS' d).symm
  refine ⟨C, ?_⟩
  have he := affineLinearExchange_action_naturality A sq
    sa
    sa'
    hw
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
    ((affineTraceRight A N hA S' d).obj (ordinaryFiniteUnit A S'))
    (affineLinearCoefficientPullback A N hA t S hS d _
      (sa.w.trans (Category.comp_id _))).hom
    (affineLinearCoefficientPullback A N hA t S' hS' d _
      (sa'.w.trans (Category.comp_id _))).hom
    (coefficientBaseChange A N hA t f hS hS' d).hom
    (coefficientBaseChange_equivariant A N hA t f hS hS' d _ _
      (sa.w.trans (Category.comp_id _))
      (sa'.w.trans (Category.comp_id _))
      hw)
  have h := congrArg (fun z ↦
    (ordinaryFinitePullback A f).map
      (affineLinearCompactComparison N hN A hA S hS d).hom ≫ z ≫
        (affineLinearCompactComparison N hN A hA S' hS' d).inv) he
  simp only [C, B, affineLinearTraceAction,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, pullback_id_eq]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id,
    Functor.map_comp, Iso.inv_hom_id_assoc]
  simpa only [Functor.map_comp, Category.assoc] using h

private lemma eq_id_of_conjugate
    {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) (r : X ⟶ X)
    (hr : e.inv ≫ r ≫ e.hom = 𝟙 Y) : r = 𝟙 X := by
  apply (cancel_epi e.inv).mp
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id] using hr

private lemma eq_id_of_homology_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K : _root_.DerivedCategory C} {M : C}
    (e : K ≅ (_root_.DerivedCategory.singleFunctor C 0).obj M)
    (r : K ⟶ K)
    (hr : (_root_.DerivedCategory.homologyFunctor C 0).map r = 𝟙 _) : r = 𝟙 _ := by
  let F := _root_.DerivedCategory.singleFunctor C 0
  let H := _root_.DerivedCategory.homologyFunctor C 0
  obtain ⟨g, hg⟩ := F.map_surjective (e.inv ≫ r ≫ e.hom)
  have : (F ⋙ H).Faithful := Functor.Faithful.of_iso
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).symm
  have hg' : g = 𝟙 M := (F ⋙ H).map_injective (by
    change H.map (F.map g) = H.map (F.map (𝟙 M))
    rw [hg, H.map_comp, H.map_comp, hr, Category.id_comp, ← H.map_comp,
      Iso.inv_hom_id, H.map_id, F.map_id, H.map_id])
  apply eq_id_of_conjugate e r
  exact hg.symm.trans (by rw [hg', F.map_id])

private lemma map_eq_id_of_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ D) (P : D ⥤ D') (Q : C ⥤ C') (G : C' ⥤ D') [G.Faithful]
    (c : F ⋙ P ≅ Q ⋙ G) {U : C} (g : U ⟶ U)
    (hg : P.map (F.map g) = 𝟙 _) : Q.map g = 𝟙 _ := by
  let e : P.obj (F.obj U) ≅ G.obj (Q.obj U) := c.app U
  have h : P.map (F.map g) ≫ e.hom = e.hom ≫ G.map (Q.map g) :=
    c.hom.naturality g
  rw [hg] at h
  have h' : e.hom = e.hom ≫ G.map (Q.map g) :=
    (Category.id_comp e.hom).symm.trans h
  apply G.map_injective
  exact ((cancel_epi e.hom).mp
    (h'.symm.trans (Category.comp_id e.hom).symm)).trans (G.map_id _).symm

private lemma eq_id_of_geometric_pullbacks
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    {K : DerivedCategoryModule A S}
    (e : K ≅ ordinaryFiniteUnit A S) (r : K ⟶ K)
    (hr : ∀ s : S, (ordinaryFinitePullback A (S.algClosurePoint s)).map r = 𝟙 _) :
    r = 𝟙 _ := by
  let F := _root_.DerivedCategory.singleFunctor
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let U := ordinaryFiniteConstant A S
  obtain ⟨g, hg⟩ := F.map_surjective (e.inv ≫ r ≫ e.hom)
  have hfaith : JointlyFaithful (fun s : S ↦ upperStar (ModuleCat.{u + 1} A)
      (S.algClosurePoint s)) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro P Q z hz
    exact isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A)
      (fun s : S ↦ S.algClosurePoint s) (fun s ↦ ⟨s, default, by simp⟩) z hz
  have hg' : g = 𝟙 U := hfaith.map_injective (fun s ↦ by
    let c := singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A)
      (S.algClosurePoint s)
    have h₁ : (ordinaryFinitePullback A (S.algClosurePoint s)).map (F.map g) = 𝟙 _ := by
      rw [hg, Functor.map_comp, Functor.map_comp, hr s, Category.id_comp,
        ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    have hp := map_eq_id_of_comparison F (ordinaryFinitePullback A (S.algClosurePoint s))
      (upperStar (ModuleCat.{u + 1} A) (S.algClosurePoint s))
      (_root_.DerivedCategory.singleFunctor _ 0) c g h₁
    exact hp.trans ((upperStar (ModuleCat.{u + 1} A) (S.algClosurePoint s)).map_id U).symm)
  apply eq_id_of_conjugate e r
  exact hg.symm.trans (by rw [hg', F.map_id]; rfl)

private lemma pullback_auto
    {C : Type*} [Category C] {P X Y Z : C}
    {v : P ⟶ X} {q : P ⟶ Y} {p : X ⟶ Z} {f : Y ⟶ Z}
    (sq : IsPullback v q p f) (e : X ≅ X) (he : e.hom ≫ p = p) :
    ∃ e' : P ≅ P, e'.hom ≫ v = v ≫ e.hom ∧ e'.hom ≫ q = q := by
  have hei : e.inv ≫ p = p := by
    calc
      e.inv ≫ p = e.inv ≫ (e.hom ≫ p) := by rw [he]
      _ = p := by simp
  let a := sq.lift (v ≫ e.hom) q (by rw [Category.assoc, he]; exact sq.w)
  let b := sq.lift (v ≫ e.inv) q (by rw [Category.assoc, hei]; exact sq.w)
  have av : a ≫ v = v ≫ e.hom := sq.lift_fst _ _ _
  have aq : a ≫ q = q := sq.lift_snd _ _ _
  have bv : b ≫ v = v ≫ e.inv := sq.lift_fst _ _ _
  have bq : b ≫ q = q := sq.lift_snd _ _ _
  have hab : a ≫ b = 𝟙 P := by
    apply sq.hom_ext
    · rw [Category.assoc, bv, ← Category.assoc, av]
      simp
    · rw [Category.assoc, bq, aq, Category.id_comp]
  have hba : b ≫ a = 𝟙 P := by
    apply sq.hom_ext
    · rw [Category.assoc, av, ← Category.assoc, bv]
      simp
    · rw [Category.assoc, aq, bq, Category.id_comp]
  exact ⟨⟨a, b, hab, hba⟩, av, aq⟩

/-- The geometric degree-one calculation for an arbitrary affine-space isomorphism makes
the induced compact-support action the identity.

Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2; fixed-base presentation invariance,
proof step 1 (blueprint: affine-space trace invariance core).

Proof: compact-support base change and the canonical coefficient descent identify the
action on a geometric stalk with pullback on the top compact-support class of affine
d-space over a separably closed field. The ordered one-dimensional Kummer normalization
sends every rational point class to one; the open-closed sequence for the projective line
and induction over the coordinate tower show that these classes generate the top group.
An isomorphism carries a rational point to its unique inverse image with local
multiplicity one, so it fixes the normalized generator. Thus the action is the identity
on every geometric stalk. The degree-zero single functor is faithful and geometric
stalks are conservative, giving the derived equality. The cases d=0, an empty base,
and the zero coefficient ring use the identity and zero-object equations.
-/
theorem affineSpaceIsoTraceAction_eq_id (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ)
    (e : affineTraceTower S d ≅ affineTraceTower S d)
    (sq : IsPullback e.hom (affineTraceProjection S d)
      (affineTraceProjection S d) (𝟙 S)) :
    affineLinearTraceAction N hN A hA t S hS d e.hom sq = 𝟙 _ := by
  obtain ⟨t₀, D₀, _, h₀⟩ := exists_affineSpaceTopTrace N hN A hA
  have sourceIso (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (N : Γ(T, ⊤))) :
      (affineTraceLeft A T d).obj
          ((affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T)) ≅
        ordinaryFiniteUnit A T := by
    haveI := (h₀ T hT d).2.2.1
    exact asIso (affineTraceCounit A N hA t₀ D₀ T hT d)
  apply eq_id_of_geometric_pullbacks A S (sourceIso S hS)
  intro s
  let f := S.algClosurePoint s
  let hS' := affineTracePullbackInvertible N f hS
  obtain ⟨e', hw, hover⟩ := pullback_auto (affineTraceMap_isPullback f d) e
    (sq.w.trans (Category.comp_id _))
  have sa' : IsPullback e'.hom (affineTraceProjection _ d)
      (affineTraceProjection _ d) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hover⟩
  obtain ⟨C, hC⟩ := action_baseChange N hN A hA t f hS hS' d
    e.hom e'.hom sq sa' hw
  have he' : affineLinearTraceAction N hN A hA t _ hS' d e'.hom sa' = 𝟙 _ :=
    eq_id_of_homology_zero (sourceIso _ hS') _
      (affineSpaceIsoTraceAction_homology_zero N hN A hA t
        (AlgebraicClosure (S.residueField s)) hS' d e' sa')
  rw [he', Category.comp_id] at hC
  exact (cancel_mono C.hom).mp (by simpa using hC)

end AlgebraicGeometry.Etale
