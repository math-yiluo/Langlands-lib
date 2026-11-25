/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateComparisons
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.HorizontalInverseSquareFixedPasting

/-! # Rectangle inverse mate with fixed endpoint comparisons

Source: Stacks Project, Tag 0ATR, proof of Lemma 48.5.2; Tag 0ATM.
(blueprint: lem-sc-horizontal-rectangle-inverse-mate-fixed-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

private theorem mate_reindex
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H H' : D ⥤ F} (s : G' ⟶ G) (b : H' ⟶ H)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare G' L₁ L₂ H')
    (h : ∀ x, L₂.map (s.app x) ≫ α.app x = β.app x ≫ b.app (L₁.obj x))
    (y : D) :
    s.app (R₁.obj y) ≫ (mateEquiv a₁ a₂ α).app y =
      (mateEquiv a₁ a₂ β).app y ≫ R₂.map (b.app y) := by
  apply (a₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit]
  have hc := a₂.counit.naturality (b.app y)
  change L₂.map (R₂.map (b.app y)) ≫ a₂.counit.app _ =
    a₂.counit.app _ ≫ b.app y at hc
  rw [hc]
  rw [← Category.assoc (L₂.map ((mateEquiv a₁ a₂ β).app y)),
    mateEquiv_counit, Category.assoc]
  rw [← Category.assoc, h, Category.assoc]
  exact congrArg (fun z ↦ β.app (R₁.obj y) ≫ z)
    (b.naturality (a₁.counit.app y)).symm

private theorem endpoint_cancel
    {C : Type*} [Category* C] {A B D E F : C}
    (s : A ≅ B) (r : F ≅ D) (b : E ≅ F) (G : B ⟶ D) (M : A ⟶ E)
    (h : s.hom ≫ G ≫ r.inv = M ≫ b.hom) :
    G ≫ r.inv ≫ b.inv = s.inv ≫ M := by
  apply (cancel_epi s.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_mono b.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h


private theorem fixed_mate_transport
    {C D Q Z P : Type*} [Category* C] [Category* D] [Category* Q]
    [Category* Z] [Category* P]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : Q ⥤ Z} {R₂ : Z ⥤ Q}
    {L₃ : P ⥤ Z} {R₃ : Z ⥤ P} {G : C ⥤ Q} {G' : C ⥤ P}
    {T : Q ⥤ P} {B B' : D ⥤ Z}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (s : G' ≅ G ⋙ T) (r : R₃ ≅ R₂ ⋙ T) (b : B' ≅ B)
    (τ : TwoSquare G L₁ L₂ B) (σ : TwoSquare G' L₁ L₃ B')
    (h : ∀ x, L₃.map (s.hom.app x) ≫
        (τ ≫ₕ (mateEquiv a₂ a₃).symm (r.inv ≫ (Functor.leftUnitor R₃).inv)).app x =
      σ.app x ≫ b.hom.app (L₁.obj x)) (y : D) :
    T.map ((mateEquiv a₁ a₂ τ).app y) ≫ r.inv.app (B.obj y) ≫ R₃.map (b.inv.app y) =
      s.inv.app (R₁.obj y) ≫ (mateEquiv a₁ a₃ σ).app y := by
  let κ := (mateEquiv a₂ a₃).symm (r.inv ≫ (Functor.leftUnitor R₃).inv)
  let b' := b.hom ≫ (Functor.rightUnitor B).inv
  have h' : ∀ x, L₃.map (s.hom.app x) ≫ (τ ≫ₕ κ).app x =
      σ.app x ≫ b'.app (L₁.obj x) := by
    simpa only [b', NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Category.comp_id] using h
  have hm := mate_reindex a₁ a₃ s.hom b' (τ ≫ₕ κ) σ h' y
  have hv := congrArg (fun α ↦ α.app y) (mateEquiv_vcomp a₁ a₂ a₃ τ κ)
  simp only [κ, Equiv.apply_symm_apply, TwoSquare.vComp_app,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Category.comp_id] at hv
  change (mateEquiv a₁ a₃ (τ ≫ₕ κ)).app y =
    T.map ((mateEquiv a₁ a₂ τ).app y) ≫ r.inv.app (B.obj y) at hv
  erw [hv] at hm
  simp only [b', NatTrans.comp_app, Functor.rightUnitor_inv_app, Category.comp_id] at hm
  exact endpoint_cancel (s.app (R₁.obj y)) (r.app (B.obj y)) (R₃.mapIso (b.app y))
    (T.map ((mateEquiv a₁ a₂ τ).app y)) ((mateEquiv a₁ a₃ σ).app y) hm

private theorem qc_pullback_eq
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    horizontalMatePullback f = qcPullback f := rfl

private theorem qc_comp_hom_map
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : schemeDerivedQCohCategory Z) :
    (schemeDerivedQCohProperty X).ι.map ((horizontalMateComp f g).hom.app E) =
      (horizontalMateAmbientComp f g).hom.app E.obj := by
  simp only [horizontalMateComp, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  rfl

private theorem qc_comp_inv_map
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : schemeDerivedQCohCategory Z) :
    (schemeDerivedQCohProperty X).ι.map ((horizontalMateComp f g).inv.app E) =
      (horizontalMateAmbientComp f g).inv.app E.obj := by
  simp only [horizontalMateComp, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage]
  rfl
private theorem source_inv_map
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : Z ⟶ Y')
    (E : schemeDerivedQCohCategory X) :
    let s := horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
      eqToIso (congrArg horizontalMatePullback
        (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
      (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
        (pullback.fst f (h ≫ g))).symm
    (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map (s.inv.app E) =
      (horizontalMateSourceIso f g h E.obj).inv := by
  intro s
  simp only [s, horizontalMateSourceIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, eqToIso.inv, eqToHom_app,
    eqToHom_map, qc_comp_hom_map, qc_comp_inv_map, Iso.app_inv, Iso.app_hom,
    Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Transport of the rectangle second mate to the mate of the pasted inverse ordinary
base-change square using the fixed source and target comparisons. There is no
middle right adjoint in this statement.
Source: Stacks Project, Tag 0ATR, proof of Lemma 48.5.2; Tag 0ATM.
(blueprint: lem-sc-horizontal-rectangle-inverse-mate-fixed-transport).

Proof: Transpose the ordinary rectangle base-change map under the outer
pullback/direct-image adjunction. Expand its counit definition and the two square
base-change maps. The associativity law of the pinned derived pullback composition
family and the two projection equations identify the transposes; injectivity of
the Hom equivalence gives ordinary base-change pasting. Conjugate and invert these
ordinary maps. Transport the upper adjunction through the pullback associativity
isomorphism, using the conjugate direct-image comparison. The counit compatibility
of right-adjoint uniqueness identifies this transport with
horizontalMateRightAdjointIso, hence with horizontalMateTargetIso after composing
the input pullbacks. Naturality of the units and counits gives the asserted
identity of the rectangle mate with the mate of the pasted inverse square. The
source comparison is exactly horizontalMateSourceIso by its construction from
the same composition family. No middle right adjoint, or invertibility of a second
mate, is used. All steps are natural transformation identities, so identity maps,
zero objects and empty schemes require no additional hypotheses. -/
theorem horizontal_rectangle_inverse_mate_fixed_transport
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
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
    let G := Arrow.mk ((derivedPullback (pullbackLeftPullbackSndIso f g h).hom).map
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι.map
        (@dualityEquationBaseChangeMap _ X Y Z
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f (h ≫ g) a c adjf adjc hβh K)))
    let α := @qcInverseBaseChange _ X Y Y'
      (QuasiCompact.compactSpace_of_compactSpace f)
      (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _ g hβ
    let δ := @qcInverseBaseChange _ (pullback f g) Y' Z
      (QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g))
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
      (pullback.snd f g) _ _ h hβ₂
    let M := (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
      ((mateEquiv adjf adjd (α ≫ₕ δ)).app K)
    G.hom ≫ (horizontalMateTargetIso f g h c d adjc adjd K).inv =
      (horizontalMateSourceIso f g h (a.obj K).obj).inv ≫ M := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
  have : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
  intro G α δ M
  let s := horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
    eqToIso (congrArg horizontalMatePullback
      (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
    (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
      (pullback.fst f (h ≫ g))).symm
  let r := horizontalMateRightAdjointIso (pullbackLeftPullbackSndIso f g h)
    (pullback.snd f (h ≫ g)) (pullback.snd (pullback.snd f g) h)
    (pullbackLeftPullbackSndIso_hom_snd f g h) c d adjc adjd
  let τ := qcInverseBaseChange f (h ≫ g) hβh
  have hp := horizontal_inverse_square_fixed_pasting g f hβ h c adjc hβh d adjd hβ₂
  have hqc := fixed_mate_transport
    (G := horizontalMatePullback (pullback.fst f (h ≫ g)))
    (G' := horizontalMatePullback (pullback.fst f g) ⋙
      horizontalMatePullback (pullback.fst (pullback.snd f g) h))
    (B := horizontalMatePullback (h ≫ g))
    (B' := horizontalMatePullback g ⋙ horizontalMatePullback h)
    adjf adjc adjd s r (horizontalMateComp h g)
    τ (α ≫ₕ δ) hp K
  have hS := dualityEquationBaseChangeMap_eq_inverseSquareMate
    f (h ≫ g) a c adjf adjc hβh K
  change dualityEquationBaseChangeMap f (h ≫ g) a c adjf adjc hβh K =
    (mateEquiv adjf adjc τ).app K at hS
  erw [← hS] at hqc
  have ha := (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.congr_map hqc
  simp only [Functor.map_comp] at ha
  change G.hom ≫ _ ≫ _ = _ ≫ M at ha
  have hsource := source_inv_map f g h (a.obj K)
  change (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
    (s.inv.app (a.obj K)) = (horizontalMateSourceIso f g h (a.obj K).obj).inv at hsource
  rw [hsource] at ha
  unfold horizontalMateTargetIso
  change G.hom ≫
    ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.mapIso
      (d.mapIso ((horizontalMateComp h g).app K) ≪≫
        r.app ((horizontalMatePullback (h ≫ g)).obj K))).inv = _
  rw [Functor.mapIso_inv, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    Iso.app_inv, Functor.map_comp]
  simpa only [ObjectProperty.ι_map, ObjectProperty.ι_obj, Functor.comp_obj,
    qc_pullback_eq] using ha

end AlgebraicGeometry
