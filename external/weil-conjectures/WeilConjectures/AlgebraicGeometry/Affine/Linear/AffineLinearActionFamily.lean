/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearUniversalAction
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-! # Specialization of the universal linear compact-support action

Source: linear trace invariance, proof paragraph 1.
(blueprint: lem-amb-affine-linear-action-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

private lemma coefficient_pullback_id
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCoefficientPullback A N hA t S hS d (𝟙 _) (Category.id_comp _) =
      (affineLinearPullbackId A (affineTraceTower S d)).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  ext
  simp only [affineLinearCoefficientPullback, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom]
  have hu := leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A)
    (affineTraceProjection S d) (affineLinearBaseCoefficient A N hA S d)
  have hunit :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 _)
        (affineTraceProjection S d) (affineTraceProjection S d)
        (Category.id_comp _).symm).inv.app (affineLinearBaseCoefficient A N hA S d) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) (affineTraceTower S d)).hom.app
        ((ordinaryFinitePullback A (affineTraceProjection S d)).obj
          (affineLinearBaseCoefficient A N hA S d)) := by
    apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 _)
      (affineTraceProjection S d) (affineTraceProjection S d)
      (Category.id_comp _).symm).hom.app (affineLinearBaseCoefficient A N hA S d))).mp
    simpa only [Iso.hom_inv_id_app, ordinaryFinitePullback] using hu.symm
  rw [hunit, pullback_id_eq]
  dsimp only [ordinaryFinitePullback]
  rw [(leftDerivedUpperStarId (ModuleCat.{u + 1} A)
    (affineTraceTower S d)).hom.naturality_assoc]
  simp

private lemma exchange_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (sq : IsPullback (𝟙 (affineTraceTower S d)) (affineTraceProjection S d)
      (affineTraceProjection S d) (𝟙 S))
    (K : DerivedCategoryModule A (affineTraceTower S d)) :
    (affineLinearPullbackId A S).inv.app _ ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
        ((affineLinearPullbackId A (affineTraceTower S d)).hom.app K) = 𝟙 _ := by
  let := affineTraceNoetherian S d
  have h := NatTrans.congr_app
    (unboundedEtaleCompactSupport_baseChange_id A (affineTraceProjection S d) sq) K
  have h' := congrArg (fun z ↦
    (unboundedEtaleUpperStarIdIso A S).inv.app _ ≫ z) h
  simpa [unboundedEtaleCompactSupportBaseChange, unboundedEtaleUpperStarIdIso,
    affineLinearPullbackId, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Iso.trans_hom, Iso.trans_inv, Category.assoc, Category.comp_id,
    Functor.map_comp, Iso.inv_hom_id_app_assoc] using h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma action_eq_id
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (sq : IsPullback a (affineTraceProjection S d) (affineTraceProjection S d) (𝟙 S))
    (ha : a = 𝟙 _) :
    affineLinearTraceAction N hN A hA t S hS d a sq = 𝟙 _ := by
  subst a
  unfold affineLinearTraceAction
  rw [coefficient_pullback_id]
  simp only [Iso.app_hom]
  rw [reassoc_of% exchange_id A S d sq
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))]
  exact (affineLinearCompactComparison N hN A hA S hS d).hom_inv_id

/-- The identity matrix acts as the identity on the actual trace source.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-affine-linear-action-family). -/
theorem affineLinearAction_one
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    linearActionMatrix N hN A hA t S hS d 1 = 𝟙 _ := by
  exact action_eq_id N hN A hA t S hS d _ _ (affineTraceLinearMap_one S d)

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
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    ∃ C : (ordinaryFinitePullback A f).obj (linearActionObject A N hA S d) ≅
        linearActionObject A N hA S' d,
      (ordinaryFinitePullback A f).map (linearActionMatrix N hN A hA t S hS d g) ≫
          C.hom =
        C.hom ≫ linearActionMatrix N hN A hA t S' hS' d
          (Matrix.GeneralLinearGroup.map f.appTop.hom g) := by
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
    (affineTraceLinearMap_isPullback S d g)
    (affineTraceLinearMap_isPullback S' d (Matrix.GeneralLinearGroup.map f.appTop.hom g))
    (affineTraceLinearMap_baseChange f d g)
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
    ((affineTraceRight A N hA S' d).obj (ordinaryFiniteUnit A S'))
    (affineLinearCoefficientPullback A N hA t S hS d _
      (affineTraceLinearMap_over S d g)).hom
    (affineLinearCoefficientPullback A N hA t S' hS' d _
      (affineTraceLinearMap_over S' d (Matrix.GeneralLinearGroup.map f.appTop.hom g))).hom
    (coefficientBaseChange A N hA t f hS hS' d).hom
    (coefficientBaseChange_equivariant A N hA t f hS hS' d _ _
      (affineTraceLinearMap_over S d g)
      (affineTraceLinearMap_over S' d (Matrix.GeneralLinearGroup.map f.appTop.hom g))
      (affineTraceLinearMap_baseChange f d g))
  have h := congrArg (fun z ↦
    (ordinaryFinitePullback A f).map
      (affineLinearCompactComparison N hN A hA S hS d).hom ≫ z ≫
        (affineLinearCompactComparison N hN A hA S' hS' d).inv) he
  dsimp only [linearActionObject] at ⊢
  simp only [C, B, linearActionMatrix, affineLinearTraceAction,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, pullback_id_eq]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id,
    Functor.map_comp, Iso.inv_hom_id_assoc]
  simpa only [Functor.map_comp, Category.assoc] using h

/-- The actual universal linear action restricts to the identity along the identity
section, and specializes to the actual action of every matrix, up to the compact-support
base-change comparison. No assertion about traces, scalar functions, or connectedness
is part of this statement.
Source: blueprint proposition-purity-vector-bundles, proof paragraph 1
(blueprint: lem-amb-affine-linear-action-family).

Proof: compactify each affine projection by its standard projective compactification.
The determinant-open and its tower are Noetherian and the projection is separated and
finite type, with quasi-compact compactifying open. The universal matrix and its inverse
are the coordinate matrix and its adjugate divided by the determinant. Apply
affineLinearExchange_action_naturality to the Cartesian linear-map squares. Pullback
along the section of g takes
its matrix entries to g, so the affine Cartesian squares identify the pulled-back
scheme automorphism with the specified linear map of g. Inverse-image composition
and the tensor and normalized Tate comparisons identify the coefficient maps: both
are descent of the ordered shifted Tate tensor from the base. Transport the resulting
exchange equation from bounded-below compact supports to the unbounded tower using
affineLinearCompactComparison and the restriction compatibilities in that definition.
All factors of the comparison are isomorphisms; their composite gives C. At the identity
section, the matrix becomes 1, and the normalized identity Tate comparison together
with unboundedEtaleCompactSupport_baseChange_id makes the pulled-back action the identity.
The source
coefficient is bounded below by exists_affineSpaceTopTrace; it is independent of the
chosen normalization data. Dimension zero uses the identity adjunction, and an empty
base satisfies the same equations. -/
theorem affineLinearAction_family
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∀ g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤),
      ∃ C : (ordinaryFinitePullback A
          (generalLinearOpen.lift (𝟙 S) g.val (Matrix.isUnits_det_units g))).obj
            (linearActionObject A N hA (generalLinearOpen d S).toScheme d) ≅
          linearActionObject A N hA S d,
        (ordinaryFinitePullback A
          (generalLinearOpen.lift (𝟙 S) g.val (Matrix.isUnits_det_units g))).map
            (linearActionMatrix N hN A hA t (generalLinearOpen d S).toScheme
              (linearUniversalInvertible N S hS d) d (linearUniversalMatrix S d)) ≫ C.hom =
          C.hom ≫ linearActionMatrix N hN A hA t S hS d g  := by
  intro g
  obtain ⟨C, hC⟩ := action_baseChange N hN A hA t
    (generalLinearOpen.lift (𝟙 S) g.val (Matrix.isUnits_det_units g))
    (linearUniversalInvertible N S hS d) hS d (linearUniversalMatrix S d)
  exact ⟨C, by simpa only [linearUniversalMatrix_specialize] using hC⟩

end AlgebraicGeometry.Etale
