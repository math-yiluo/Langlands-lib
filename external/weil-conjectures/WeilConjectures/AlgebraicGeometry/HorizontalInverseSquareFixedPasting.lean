/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateComparisons
public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.HorizontalOrdinaryInverseFixedPasting

/-! # Ordinary inverse-square pasting with the fixed upper transport

Source: Stacks Project, Tags 0ATM and 0ATR.
(blueprint: lem-sc-horizontal-inverse-square-fixed-pasting).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
-- The inverse mate of transported right-adjoint uniqueness is the equivalence counit.
private theorem transport_mate
    {A B T : Type*} [Category* A] [Category* B] [Category* T]
    (e : A ≌ B) {P : A ⥤ T} {Q : B ⥤ T} {c : T ⥤ A} {d : T ⥤ B}
    (ac : P ⊣ c) (ad : Q ⊣ d) (li : Q ≅ e.inverse ⋙ P) :
    let a := (e.symm.toAdjunction.comp ac).ofNatIsoLeft li.symm
    let r := ad.rightAdjointUniq a
    let κ := (mateEquiv ac ad).symm (r.inv ≫ (Functor.leftUnitor d).inv)
    ∀ K : A, κ.app K = li.hom.app (e.functor.obj K) ≫
      P.map (e.unitIso.inv.app K) := by
  intro a r κ K
  dsimp [κ, mateEquiv]
  simp only [Q.map_id, Category.id_comp, Category.comp_id]
  change Q.map (e.functor.map (ac.unit.app K)) ≫
    Q.map (r.inv.app (P.obj K)) ≫ ad.counit.app (P.obj K) = _
  rw [Adjunction.rightAdjointUniq_inv_app, Adjunction.rightAdjointUniq_hom_app_counit]
  dsimp [a, Adjunction.ofNatIsoLeft]
  rw [Adjunction.comp_counit_app]
  change Q.map (e.functor.map (ac.unit.app K)) ≫
    li.hom.app (e.functor.obj (c.obj (P.obj K))) ≫
    P.map (e.unitIso.inv.app (c.obj (P.obj K))) ≫ ac.counit.app (P.obj K) = _
  have hn := li.hom.naturality (e.functor.map (ac.unit.app K))
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← P.map_comp_assoc]
  have hu := e.unitIso.inv.naturality (ac.unit.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hu
  rw [hu]
  rw [P.map_comp, Category.assoc]
  rw [ac.left_triangle_components]
  simp

set_option backward.isDefEq.respectTransparency true in
-- Component formula for the ordinary square constructed from the inverse unit.
private theorem canonical_transfer_app
    {A B T : Type*} [Category* A] [Category* B] [Category* T]
    (e : A ≌ B) {P : A ⥤ T} {Q : B ⥤ T} (li : Q ≅ e.inverse ⋙ P) :
    let k : TwoSquare e.functor P Q (𝟭 T) := .mk _ _ _ _ <|
      (Functor.isoWhiskerLeft e.functor li).hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e.unitIso.inv P ≫
        (Functor.leftUnitor P).hom ≫ (Functor.rightUnitor P).inv
    ∀ K : A, k.app K = li.hom.app (e.functor.obj K) ≫
      P.map (e.unitIso.inv.app K) := by
  intro k K
  simp [k, TwoSquare.mk, Functor.isoWhiskerLeft_hom]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Specialize the categorical calculation to the pinned scheme comparisons.
private theorem fixed_transport_mate
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P Q Z : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (e : P ≅ Q) (q : Q ⟶ Z) (p : P ⟶ Z) [QuasiCompact q] [QuasiSeparated q]
    [QuasiCompact p] [QuasiSeparated p] (hp : e.hom ≫ q = p)
    (c : schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory Q)
    (d : schemeDerivedQCohCategory Z ⥤ schemeDerivedQCohCategory P)
    (ac : horizontalMatePushforward q ⊣ c) (ad : horizontalMatePushforward p ⊣ d) :
    let ev := horizontalMateEquivalence e
    let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
    let li := eqToIso (congrArg qcDirectImage hp.symm) ≪≫
      horizontalMatePushComp e.hom q ≪≫
      Functor.isoWhiskerRight ri (horizontalMatePushforward q)
    let r := horizontalMateRightAdjointIso e q p hp c d ac ad
    let κ := (mateEquiv ac ad).symm (r.inv ≫ (Functor.leftUnitor d).inv)
    let k : TwoSquare (horizontalMatePullback e.hom)
        (horizontalMatePushforward q) (horizontalMatePushforward p)
        (𝟭 (schemeDerivedQCohCategory Z)) := .mk _ _ _ _ <|
      (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
        (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
        (Functor.rightUnitor (horizontalMatePushforward q)).inv
    κ = k := by
  subst p
  intro ev ri li r κ k
  refine NatTrans.ext (funext fun K ↦ ?_)
  have ht := transport_mate ev ac ad (horizontalMatePushComp e.hom q ≪≫
    Functor.isoWhiskerRight ri (horizontalMatePushforward q)) K
  have hc := canonical_transfer_app ev (horizontalMatePushComp e.hom q ≪≫
    Functor.isoWhiskerRight ri (horizontalMatePushforward q)) K
  dsimp only [Equivalence.symm_inverse] at ht hc
  dsimp only [ev, horizontalMateEquivalence, CategoryTheory.Equivalence.mk] at ht hc
  dsimp only [κ, r, horizontalMateRightAdjointIso, k, li, ev,
    horizontalMateEquivalence, CategoryTheory.Equivalence.mk, eqToIso_refl]
  simp only [Iso.refl_trans]
  exact ht.trans hc.symm



private theorem horizontalOrdinaryTransfer_eq
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P Q Z : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (e : P ≅ Q) (q : Q ⟶ Z) (p : P ⟶ Z)
    [QuasiCompact q] [QuasiSeparated q] [QuasiCompact p] [QuasiSeparated p]
    (hp : e.hom ≫ q = p) :
    horizontalOrdinaryTransfer e q p hp =
    (let ev := horizontalMateEquivalence e
  let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
  let li := eqToIso (congrArg qcDirectImage hp.symm) ≪≫
    horizontalMatePushComp e.hom q ≪≫
    Functor.isoWhiskerRight ri (horizontalMatePushforward q)
  .mk _ _ _ _ <|
    (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
      (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
      (Functor.rightUnitor (horizontalMatePushforward q)).inv) := by rfl

private theorem horizontalOrdinaryUpperComparison_eq
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}} (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S) :
    horizontalOrdinaryUpperComparison f g h =
    (horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
    eqToIso (congrArg horizontalMatePullback
      (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
    (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
      (pullback.fst f (h ≫ g))).symm) := by rfl

private theorem horizontalOrdinaryBaseComparison_eq
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {Y S T : Scheme.{u}} (g : S ⟶ Y) (h : T ⟶ S) :
    horizontalOrdinaryBaseComparison g h =
    (horizontalMateComp h g) := by rfl

/-- The pasted inverse ordinary square agrees with the rectangle inverse square,
after changing its upper projection and base pullback by the pinned comparisons.
This statement involves no right adjoint to the bottom direct image.
Source: Stacks Project, Remark 20.28.5 (Tag 0ATM), and Lemma 48.5.2 (Tag 0ATR).
(blueprint: lem-sc-horizontal-inverse-square-fixed-pasting).

Proof: Transpose the rectangle ordinary square and the horizontal composite under
pullback along the outer upper projection. Expand schemeDerivedBaseChangeMap as
its defining counit transpose. Naturality moves each composition comparison past
the counit. Apply associativity of the pinned pullback composition family to the
base chain h,g and to the upper projection chain. The two projection equations
of pullbackLeftPullbackSndIso identify the resulting maps; injectivity of the
adjunction Hom equivalence gives ordinary pasting. Invert these ordinary squares.
The comparison of direct images along the upper scheme isomorphism is the
conjugate of the pinned pullback comparison. Its right-adjoint comparison is
horizontalMateRightAdjointIso: use rightAdjointUniq_hom_app_counit for the
transported adjunction, then the equivalence triangle identities. Consequently
its inverse ordinary square is the inverse mate of that right-adjoint comparison.
Whiskering the inverted ordinary pasting equation with the two pullback
comparisons gives the displayed identity. All comparisons are natural, and all
cancellations invert only ordinary squares or the displayed isomorphisms; zero
objects, identity morphisms and empty schemes are included. -/
theorem horizontal_inverse_square_fixed_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y')
    (c : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (adjc : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (h ≫ g))) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _ _ _
          (pullback.snd f (h ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (d : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adjd : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h))
          _ _ _ _ (pullback.snd (pullback.snd f g) h) _ _).fst E.obj E.property) ⊣ d)
    (hβ₂ : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj)) :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
      eqToIso (congrArg horizontalMatePullback
        (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
      (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
        (pullback.fst f (h ≫ g))).symm
    let r := horizontalMateRightAdjointIso (pullbackLeftPullbackSndIso f g h)
      (pullback.snd f (h ≫ g)) (pullback.snd (pullback.snd f g) h)
      (pullbackLeftPullbackSndIso_hom_snd f g h) c d adjc adjd
    let κ := (mateEquiv adjc adjd).symm
      (r.inv ≫ (Functor.leftUnitor d).inv)
    let τ := qcInverseBaseChange f (h ≫ g) hβh
    let σ := qcInverseBaseChange f g hβ ≫ₕ
      @qcInverseBaseChange _ (pullback f g) Y' Z _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβ₂
    ∀ E : schemeDerivedQCohCategory X,
      (horizontalMatePushforward (pullback.snd (pullback.snd f g) h)).map
          (s.hom.app E) ≫ (τ ≫ₕ κ).app E =
        σ.app E ≫ (horizontalMateComp h g).hom.app
          ((horizontalMatePushforward f).obj E) := by
  set_option backward.isDefEq.respectTransparency true in
   set_option backward.isDefEq.respectTransparency.types true in
    classical
    let : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    let : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)
    intro s r κ τ σ E
    have hk := fixed_transport_mate (pullbackLeftPullbackSndIso f g h)
      (pullback.snd f (h ≫ g)) (pullback.snd (pullback.snd f g) h)
      (pullbackLeftPullbackSndIso_hom_snd f g h) c d adjc adjd
    have ho := horizontal_ordinary_inverse_fixed_pasting g f hβ h hβh hβ₂ E
    simp only [horizontalOrdinaryTransfer_eq, horizontalOrdinaryUpperComparison_eq,
      horizontalOrdinaryBaseComparison_eq, s, r, κ, τ, σ, ← hk, TwoSquare.mk] at ho ⊢
    convert ho using 1
    rfl

end AlgebraicGeometry
