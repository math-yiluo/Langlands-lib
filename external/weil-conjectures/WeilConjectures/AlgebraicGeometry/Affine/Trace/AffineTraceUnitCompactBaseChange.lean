/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction

import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction

/-! # Base change of the compact-support comparison at the affine Tate coefficient

Source: blueprint vector integration, overlap calculation, transport of tower exchange.
(blueprint: lem-amb-affine-trace-unit-compact-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open scoped CategoryTheory.Functor

attribute [local irreducible]
  rightDerivedLowerShriekOfCompactificationIso
  rightDerivedLowerShriekOfCompactificationPlusIso
  unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekId
  rightDerivedLowerShriekPlusCompIso
  upperStar affineTraceUnboundedCompactComparison

private lemma iso_id_map {C : Type*} [Category C] {F : C ⥤ C}
    (e : F ≅ 𝟭 C) (K : C) : e.hom.app (F.obj K) = F.map (e.hom.app K) := by
  apply (cancel_mono (e.hom.app K)).mp
  exact (e.hom.naturality (e.hom.app K)).symm

private lemma identity_exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S)
    (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
        ((unboundedEtaleLowerShriekId A S).inv.app K) ≫
      (unboundedEtaleCompactSupportBaseChange A (IsPullback.id_vert f)).app K =
    (unboundedEtaleLowerShriekId A T).inv.app
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K) := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S)
  let G := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T)
  let P := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  let C := unboundedEtaleCompactSupportBaseChange A (IsPullback.id_vert f)
  have : IsIso C := (unboundedEtaleCompactSupport_baseChange A (IsPullback.id_vert f)).1
  have : G.Faithful := Functor.Faithful.of_iso (unboundedEtaleLowerShriekId A T).symm
  have h := congr_app (unboundedEtaleCompactSupport_baseChange_composition A
    (IsPullback.id_vert f) (IsPullback.id_vert f)
    (IsPullback.id_vert f)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp] at h
  have hs := congr_app (unboundedEtaleLowerShriekCompIso_units A (𝟙 S)).2 K
  have ht := congr_app (unboundedEtaleLowerShriekCompIso_units A (𝟙 T)).2 (P.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, unboundedEtaleLowerShriekCongr,
    Iso.refl_hom, Category.comp_id] at hs ht
  rw [iso_id_map (unboundedEtaleLowerShriekId A S) K] at hs
  rw [iso_id_map (unboundedEtaleLowerShriekId A T) (P.obj K)] at ht
  change (unboundedEtaleLowerShriekCompIso A (𝟙 S) (𝟙 S)).hom.app K =
    F.map ((unboundedEtaleLowerShriekId A S).hom.app K) ≫ 𝟙 _ at hs
  change (unboundedEtaleLowerShriekCompIso A (𝟙 T) (𝟙 T)).hom.app (P.obj K) =
    G.map ((unboundedEtaleLowerShriekId A T).hom.app (P.obj K)) ≫ 𝟙 _ at ht
  simp only [Category.comp_id] at hs ht
  rw [hs, ht] at h
  have hn := C.naturality ((unboundedEtaleLowerShriekId A S).hom.app K)
  simp only [Functor.comp_map] at hn
  erw [hn] at h
  have he : P.map ((unboundedEtaleLowerShriekId A S).hom.app K) =
      C.app K ≫ (unboundedEtaleLowerShriekId A T).hom.app (P.obj K) := by
    apply G.map_injective
    simpa only [Functor.map_comp] using (cancel_epi (C.app (F.obj K))).mp h
  apply (cancel_mono ((unboundedEtaleLowerShriekId A T).hom.app (P.obj K))).mp
  simp only [Category.assoc]
  erw [← he, ← P.map_comp, Iso.inv_hom_id_app, P.map_id, Iso.inv_hom_id_app]
  rfl

private lemma identity_exchange_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A f).map ((unboundedEtaleLowerShriekId A S).inv.app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A (IsPullback.id_vert f)).app K =
    (unboundedEtaleLowerShriekId A T).inv.app ((ordinaryFinitePullback A f).obj K) := by
  let u := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T)
  have h := identity_exchange A f K
  simp only [unboundedEtaleCompactSupportBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  apply (cancel_epi (u.inv.app K)).mp
  apply (cancel_mono (R.map (u.hom.app K))).mp
  simp only [Category.assoc]
  have hn := u.inv.naturality ((unboundedEtaleLowerShriekId A S).inv.app K)
  erw [← reassoc_of% hn]
  erw [h]
  have ht := (unboundedEtaleLowerShriekId A T).inv.naturality (u.hom.app K)
  simp only [Functor.id_map] at ht
  erw [← ht, Iso.inv_hom_id_app_assoc]

section
attribute [local irreducible] rightDerivedLowerShriek rightDerivedLowerShriekBaseChangeMap

private lemma composition_exchange_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    [IsNoetherian Z] [IsNoetherian Z']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ)
    (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A vZ).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A sqgf).app K =
    (rightDerivedLowerShriekBaseChangeMap A sqg).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g').map
        ((rightDerivedLowerShriekBaseChangeMap A sqf).app K) ≫
      (unboundedEtaleLowerShriekCompIso A f' g').hom.app
        ((ordinaryFinitePullback A vX).obj K) := by
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g'
  let H := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f' ≫ g')
  let u := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) vZ
  let v := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) vY
  let w := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) vX
  let a := unboundedEtaleLowerShriekCompIso A f g
  let a' := unboundedEtaleLowerShriekCompIso A f' g'
  have h := congr_app
    (unboundedEtaleCompactSupport_baseChange_composition A sqf sqg sqgf) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, unboundedEtaleCompactSupportBaseChange, Functor.map_comp,
    Category.assoc] at h
  apply (cancel_epi (u.inv.app ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K)))).mp
  apply (cancel_mono (H.map (w.hom.app K))).mp
  have hn := u.inv.naturality (a.hom.app K)
  erw [← reassoc_of% hn]
  simp only [Category.assoc]
  erw [h]
  have ha := a'.hom.naturality (w.hom.app K)
  simp only [Functor.comp_map] at ha
  erw [ha]
  erw [← R.map_comp_assoc, Iso.hom_inv_id_app, R.map_id, Category.id_comp]
  rfl

end

private lemma composition_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : T ⟶ S) (d : ℕ)
    (K : DerivedCategoryModule A (affineTraceTower S (d + 1))) :
    (ordinaryFinitePullback A f).map
        ((unboundedEtaleLowerShriekCompIso A
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
          (affineTraceProjection S d)).hom.app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A (affineTraceMap_isPullback f (d + 1))).app K =
    (rightDerivedLowerShriekBaseChangeMap A (affineTraceMap_isPullback f d)).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
        ((rightDerivedLowerShriekBaseChangeMap A
          (AffineSpace.isPullback_map (n := PUnit.{u + 1}) (affineTraceMap f d))).app K) ≫
      (unboundedEtaleLowerShriekCompIso A
        (AffineSpace PUnit.{u + 1} (affineTraceTower T d) ↘ affineTraceTower T d)
        (affineTraceProjection T d)).hom.app
          ((ordinaryFinitePullback A (affineTraceMap f (d + 1))).obj K) := by
  let := affineTraceNoetherian S d
  let := affineTraceNoetherian T d
  have : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
    affineTraceNoetherian S (d + 1)
  have : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower T d)) :=
    affineTraceNoetherian T (d + 1)
  exact composition_exchange_general A
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) (affineTraceMap f d))
    (affineTraceMap_isPullback f d) (affineTraceMap_isPullback f (d + 1)) K

private lemma line_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S)
    (K : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    (ordinaryFinitePullback A f).map
        ((rightDerivedLowerShriekIso A (affineTraceLineCompactification S)).hom.app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A
        (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)).app K =
    affineTraceLineExchange A f K ≫
      (rightDerivedLowerShriekIso A (affineTraceLineCompactification T)).hom.app
        ((ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj K) := by
  have : IsNoetherian (AffineSpace PUnit.{u + 1} S) := affineTraceNoetherian S 1
  have : IsNoetherian (AffineSpace PUnit.{u + 1} T) := affineTraceNoetherian T 1
  let sq := AffineSpace.isPullback_map (n := PUnit.{u + 1}) f
  let c := affineTraceLineCompactification S
  let c' := affineTraceLineCompactification T
  let q' := AffineSpace PUnit.{u + 1} T ↘ T
  let u := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let v := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
    (AffineSpace.map PUnit.{u + 1} f)
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) q'
  have hc := congr_app (congrArg Iso.hom
    ((unboundedEtaleCompactSupport_comparison_coherence A q').2
      (c.ofIsPullback sq) c' (HasCompactification.compactification q')))
        ((ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj K)
  simp only [Iso.trans_hom, NatTrans.comp_app] at hc
  erw [affineTraceLineExchange_eq, Category.assoc, hc]
  have h := congr_app ((unboundedEtaleCompactSupport_baseChange A sq).2 c) K
  simp only [unboundedEtaleCompactSupportBaseChange, unboundedEtaleCompactSupportExchange,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at h
  apply (cancel_epi (u.inv.app
    ((affineTraceLineLeft A S).obj K))).mp
  apply (cancel_mono (R.map (v.hom.app K))).mp
  simp only [Category.assoc]
  have hn := u.inv.naturality ((rightDerivedLowerShriekIso A c).hom.app K)
  erw [← reassoc_of% hn, h]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  have ht := (rightDerivedLowerShriekIso A (c.ofIsPullback sq)).hom.naturality
    (v.hom.app K)
  simp only [Functor.comp_map] at ht
  erw [ht]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private lemma exchange_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) (d : ℕ)
    {K M : DerivedCategoryModule A (affineTraceTower S d)} (a : K ⟶ M) :
    (ordinaryFinitePullback A f).map ((affineTraceLeft A S d).map a) ≫
      affineTraceExchange A f d M =
    affineTraceExchange A f d K ≫
      (affineTraceLeft A T d).map ((ordinaryFinitePullback A (affineTraceMap f d)).map a) := by
  unfold affineTraceExchange
  exact (affineTraceExchangeTower
    (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (C' := fun d ↦ DerivedCategoryModule A (affineTraceTower T d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower S d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower T d))
    (fun d ↦ ordinaryFinitePullback A (affineTraceMap f d))
    (fun d ↦ affineTraceLineExchangeTransformation A (affineTraceMap f d)) d).naturality a

private lemma exchange_succ
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) (d : ℕ)
    (K : DerivedCategoryModule A (affineTraceTower S (d + 1))) :
    affineTraceExchange A f (d + 1) K =
      affineTraceExchange A f d ((affineTraceLineLeft A (affineTraceTower S d)).obj K) ≫
        (affineTraceLeft A T d).map (affineTraceLineExchange A (affineTraceMap f d) K) := by
  simp only [affineTraceExchange, affineTraceExchangeTower_succ, affineTraceLineExchange]

private lemma tower_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : T ⟶ S) (d : ℕ) (K : DerivedCategoryModule A (affineTraceTower S d)) :
    (ordinaryFinitePullback A f).map ((affineTraceUnboundedCompactComparison A S d).hom.app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A (affineTraceMap_isPullback f d)).app K =
    affineTraceExchange A f d K ≫
      (affineTraceUnboundedCompactComparison A T d).hom.app
        ((ordinaryFinitePullback A (affineTraceMap f d)).obj K) := by
  induction d with
  | zero =>
    simp only [affineTraceUnboundedCompactComparison]
    change (ordinaryFinitePullback A f).map
      ((unboundedEtaleLowerShriekId A S).inv.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A (IsPullback.id_vert f)).app K =
      (𝟙 _ ≫ 𝟙 _) ≫ (unboundedEtaleLowerShriekId A T).inv.app
        ((ordinaryFinitePullback A f).obj K)
    simpa only [Category.id_comp] using identity_exchange_left A f K
  | succ d ih =>
    let := affineTraceNoetherian S d
    let := affineTraceNoetherian T d
    let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
    let q' := AffineSpace PUnit.{u + 1} (affineTraceTower T d) ↘ affineTraceTower T d
    let c := affineTraceLineCompactification (affineTraceTower S d)
    let c' := affineTraceLineCompactification (affineTraceTower T d)
    let e := rightDerivedLowerShriekIso A c
    let e' := rightDerivedLowerShriekIso A c'
    let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) q
    let R' := rightDerivedLowerShriek (ModuleCat.{u + 1} A) q'
    let P := ordinaryFinitePullback A (affineTraceMap f d)
    let P' := ordinaryFinitePullback A (affineTraceMap f (d + 1))
    let E := (rightDerivedLowerShriekBaseChangeMap A
      (AffineSpace.isPullback_map (n := PUnit.{u + 1}) (affineTraceMap f d))).app K
    have hn := (affineTraceUnboundedCompactComparison A T d).hom.naturality E
    simp only [affineTraceUnboundedCompactComparison, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.map_comp, Category.assoc, exchange_succ]
    erw [composition_exchange, reassoc_of% ih (R.obj K)]
    erw [reassoc_of% exchange_naturality A f d (e.hom.app K)]
    erw [← reassoc_of% hn]
    erw [← (affineTraceLeft A T d).map_comp_assoc,
      line_exchange A (affineTraceMap f d) K]
    simp only [Functor.map_comp, Category.assoc]
    rfl

private lemma comparison_eq
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCompactComparison N hN A hA S hS d =
      (affineTraceUnboundedCompactComparison A S d).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  apply Iso.ext
  change (affineTracePlusCompatibility A S d).inv.app K ≫
    DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).hom.app K =
    (affineTraceUnboundedCompactComparison A S d).hom.app (DerivedCategory.Plus.ι.obj K)
  apply (cancel_epi ((affineTracePlusCompatibility A S d).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (affineTraceUnboundedCompactComparison_restriction A S d K).symm

/-- The comparison with ordinary compact supports intertwines tower exchange at the
canonical Tate coefficient with ordinary exchange and its canonical coefficient map.
There is no vector bundle, frame or inverse-chart square in this statement.
Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md,
overlap calculation, comparison of coordinate-tower exchange with ordinary exchange.
(blueprint: lem-amb-affine-trace-unit-compact-base-change).

Proof: express the ordered tower comparison on bounded-below objects by the recursive
compactification comparison followed by the compact-support compositor. At zero the
comparison is inverse to the compact-support identity comparison, and exchange is the
identity; the unit compatibility of compact-support exchange gives the equation.
For a successor, expand the last affine-line step. Its exchange is the proper/open
exchange on the standard projective compactification, conjugated by the comparisons
with the chosen compactification. Apply compatibility of exchange with compact-support
composition, then compactification independence to identify this conjugate with ordinary
line exchange. The preceding tower equation identifies the remaining factor. Transport
through the bounded-below inclusion using the composition and exchange compatibility
of the unbounded compact-support package. The right coefficient is bounded below by
affine-space top trace; exact pullback preserves this property. Naturality of the tower
comparison moves the isomorphism b through it, giving the displayed equation. The proof
uses only canonical comparison and exchange maps, so it also covers d=0, empty bases,
and the zero coefficient ring. -/
theorem affineTraceUnitCompactComparison_baseChange
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    let b := affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S) ≪≫
      (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A f)
    (ordinaryFinitePullback A f).map
        (affineLinearCompactComparison N hN A hA S hS d).inv ≫
      affineTraceExchange A f d
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
      (affineTraceLeft A T d).map b.hom =
    (rightDerivedLowerShriekBaseChangeMap A (affineTraceMap_isPullback f d)).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection T d)).map b.hom ≫
      (affineLinearCompactComparison N hN A hA T
        (affineTracePullbackInvertible N f hS) d).inv := by
  dsimp only
  rw [comparison_eq, comparison_eq]
  simp only [Iso.app_inv]
  let K := (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)
  let b := affineTraceRightBaseChange A N hA t f hS d (ordinaryFiniteUnit A S) ≪≫
    (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A f)
  let P := ordinaryFinitePullback A f
  have he := tower_exchange A f d K
  have hn := (affineTraceUnboundedCompactComparison A T d).hom.naturality b.hom
  apply (cancel_epi (P.mapIso ((affineTraceUnboundedCompactComparison A S d).app K)).hom).mp
  erw [← P.map_comp_assoc, Iso.hom_inv_id_app, P.map_id, Category.id_comp]
  erw [reassoc_of% he, ← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app, Category.comp_id]
  rfl

end AlgebraicGeometry.Etale
