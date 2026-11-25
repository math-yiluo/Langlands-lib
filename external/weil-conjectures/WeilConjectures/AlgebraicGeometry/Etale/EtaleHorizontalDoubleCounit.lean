/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalSupportMate
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Double counits in an etale-horizontal square

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md, Step 1;
Stacks Project, Tags 0037, 0DV0, 0F7J, 0F7K, 0F7L and 03S6
(blueprint: lem-pur-etale-horizontal-double-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar etaleLowerShriek
  Functor.mapDerivedCategory derivedEtaleLowerShriekUpperStarAdjunction

/-- The right-adjoint restriction comparison determined by inverse compact-support exchange.
Source: Stacks Project, Tags 0037 and 0F7L
(blueprint: lem-pur-etale-horizontal-double-counit). -/
noncomputable def etaleHorizontalCounitRightExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {h : X ⟶ Y} {h' : X' ⟶ Y'} {e : Y' ⟶ Y} {e' : X' ⟶ X}
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification h] [HasCompactification h'] [QuasiCompact h']
    (sq : IsPullback e' h' h e)
    {G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
    {G' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h' ⊣ G') :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙ G' :=
  (mateEquiv adj adj'
    (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A sq).inv))

private lemma conjugate_transport
    {C D : Type*} [Category* C] [Category* D]
    {L L' F : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (i : L ≅ F) (j : L' ≅ F) (t : L' ≅ L)
    (ht : t.hom ≫ i.hom = j.hom) :
    conjugateEquiv a b t.hom =
      conjugateEquiv (a.ofNatIsoLeft i) (b.ofNatIsoLeft j) (𝟙 F) := by
  ext K
  apply ((b.ofNatIsoLeft j).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, NatTrans.id_app, Category.id_comp]
  rw [← Category.assoc, j.inv.naturality]
  simp only [Category.assoc]
  rw [conjugateEquiv_counit, ← Category.assoc]
  have he : j.inv ≫ t.hom = i.inv := by
    apply (cancel_mono i.hom).1
    simp [Category.assoc, ht]
  exact congrArg (fun z ↦ z.app (R.obj K) ≫ a.counit.app K) he

private lemma mate_top
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {U U' : C ⥤ E} {V : D ⥤ F}
    (α : TwoSquare U' L L' V) (t : U ⟶ U') (K : D) :
    (mateEquiv a b (α.whiskerTop t)).app K =
      t.app (R.obj K) ≫ (mateEquiv a b α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_bottom
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {U : C ⥤ E} {V V' : D ⥤ F}
    (α : TwoSquare U L L' V) (t : V ⟶ V') (K : D) :
    (mateEquiv a b (α.whiskerBottom t)).app K =
      (mateEquiv a b α).app K ≫ R'.map (t.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, t.naturality]

private lemma mate_cube
    {C₀ D₀ C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category* C₀] [Category* D₀] [Category* C₁] [Category* D₁]
    [Category* C₂] [Category* D₂] [Category* C₃] [Category* D₃]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {L₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {U₀₁ : C₀ ⥤ C₁} {V₀₁ : D₀ ⥤ D₁} {U₁₃ : C₁ ⥤ C₃} {V₁₃ : D₁ ⥤ D₃}
    {U₀₂ : C₀ ⥤ C₂} {V₀₂ : D₀ ⥤ D₂} {U₂₃ : C₂ ⥤ C₃} {V₂₃ : D₂ ⥤ D₃}
    (α : TwoSquare U₀₁ L₀ L₁ V₀₁) (β : TwoSquare U₁₃ L₁ L₃ V₁₃)
    (γ : TwoSquare U₀₂ L₀ L₂ V₀₂) (δ : TwoSquare U₂₃ L₂ L₃ V₂₃)
    (s : U₀₁ ⋙ U₁₃ ≅ U₀₂ ⋙ U₂₃) (t : V₀₁ ⋙ V₁₃ ≅ V₀₂ ⋙ V₂₃)
    (hc : α.hComp β = ((γ.hComp δ).whiskerTop s.hom).whiskerBottom t.inv) :
    Functor.whiskerRight (mateEquiv a₀ a₁ α) U₁₃ ≫
        Functor.whiskerLeft V₀₁ (mateEquiv a₁ a₃ β) =
      Functor.whiskerLeft R₀ s.hom ≫
        Functor.whiskerRight (mateEquiv a₀ a₂ γ) U₂₃ ≫
        Functor.whiskerLeft V₀₂ (mateEquiv a₂ a₃ δ) ≫
        Functor.whiskerRight t.inv R₃ := by
  ext K
  have hh := congrArg (fun q ↦ (mateEquiv a₀ a₃ q).app K) hc
  rw [mate_bottom, mate_top, mateEquiv_vcomp, mateEquiv_vcomp] at hh
  simpa only [TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] using hh

private noncomputable def pullComp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso
    (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg)

section Square

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X X' Y Y' : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
  {h : X ⟶ Y} {h' : X' ⟶ Y'} {e : Y' ⟶ Y} {e' : X' ⟶ X}
  [IsSeparated h] [IsSeparated h'] [IsSeparated e] [IsSeparated e']
  [Etale e] [Etale e']
  [LocallyOfFiniteType h] [LocallyOfFiniteType h']
  [QuasiCompact h] [QuasiCompact h'] [QuasiCompact e] [QuasiCompact e']
  [HasCompactification h] [HasCompactification h']
  [HasCompactification e] [HasCompactification e']
  [HasCompactification (e' ≫ h)] [HasCompactification (h' ≫ e)]
  (sq : ChosenCartesianSquare e' h' h e) (N : EtaleCompactSupportNormalization A)
  {G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
  {G' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
  (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h ⊣ G)
  (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h' ⊣ G')

/-- Conjugate the specified inverse delta under the two normalized composite adjunctions.
This is the map b of the node; the compositor formula is recorded below.
Source: Stacks Project, Tags 0037 and 0DV0
(blueprint: lem-pur-etale-horizontal-double-counit). -/
noncomputable def etaleHorizontalDoubleCounitIso :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙ G' :=
  conjugateIsoEquiv
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e' inferInstance).comp adj)
    (adj'.comp (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance))
    (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).symm

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/-- Double-counit equality, single-counit equality, and the unique adjunct description.
Source: blueprint co-smooth etale locality, Step 1; Stacks 0037, 0DV0 and 0F7K
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: (1) conjugacy of d inverse preserves the evaluation/counit normalization.
(2) Conjugate the difference of the two compositors, using contravariant composition.
(3) Change from the compact-support adjunctions to the sum/evaluation adjunctions;
mate pasting identifies the resulting conjugate with b and the left map with delta inverse.
(4) Expand both composite counits by Adjunction.comp to obtain the first equality.
(5) Apply lem-pur-etale-horizontal-support-mate at G K and use counit naturality.
(6) Cancel the inverse hom bijection for the sum adjunction, obtaining the second
identity. The hom bijection for adj' gives the unique adjunct assertion.
(7) Refinement comparisons preserve d and the compositors; conjugacy preserves their
counits, so the identities transport under refinement.
(8) Exchange pasting and lem-pur-etale-support-map-compatibility identify the two
restricted mates; the sum/evaluation adjunction is the same after open restriction.
No evaluation counit is cancelled as an isomorphism. -/
theorem etaleHorizontalDoubleCounit :
    ∀ K : DerivedCategoryModule A Y,
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
              ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
            adj'.counit.app
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K =
      (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj (G.obj K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance).counit.app (G.obj K)) ≫
        adj.counit.app K) ∧
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
          ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
        adj'.counit.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) =
      (etaleHorizontalSupportBaseChangeIso A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map (adj.counit.app K)) ∧
      (adj'.homEquiv _ _
        ((etaleHorizontalSupportBaseChangeIso A
          (IsPullback.of_iso_pullback sq.toCommSq
            sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
          (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
            (adj.counit.app K)) =
        (etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) := by
  intro K
  let ae := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance
  let ae' := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e' inferInstance
  let p := IsPullback.of_iso_pullback sq.toCommSq
    sq.isoPullback sq.hom_fst sq.hom_snd
  have hd : ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
              ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
            adj'.counit.app
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K =
      (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj (G.obj K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance).counit.app (G.obj K)) ≫
        adj.counit.app K) := by
    simpa only [etaleHorizontalDoubleCounitIso, conjugateIsoEquiv_apply_hom,
      ae, ae', p, Iso.symm_hom, Adjunction.comp_counit_app, Functor.comp_obj,
      Functor.comp_map,
      Functor.map_comp, Category.assoc] using
      conjugateEquiv_counit (ae'.comp adj) (adj'.comp ae)
        (etaleHorizontalSupportMateDelta A p N).inv K
  have hs : ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
          ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
        adj'.counit.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) =
      (etaleHorizontalSupportBaseChangeIso A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map (adj.counit.app K)) := by
    apply (ae.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hd]
    rw [← Category.assoc, etaleHorizontalSupportMate A p N (G.obj K)]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    exact (ae.counit.naturality (adj.counit.app K)).symm
  refine ⟨hd, hs, ?_⟩
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact hs.symm

set_option linter.unusedSectionVars false in
/-- The explicit formula rho inverse, inverse first conjugate compositor, second
conjugate compositor, and rho. A common right adjoint for the equal composites is
arbitrary, and both occurrences use the same adjunction.
Source: Stacks 0037 and 0DV0, blueprint co-smooth etale locality Step 1
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: conjugate alpha for each composite adjunction. Contravariance identifies the
middle two factors with the conjugate of alpha_h inverse after alpha_e. Mate pasting
moves d_e inverse and d_e' across the composite adjunctions. These are exactly rho_e
and rho_e' inverse, respectively, giving the defining conjugate of delta inverse. -/
theorem etaleHorizontalDoubleCounit_compositors
    {Ge : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A Y'}
    {Ge' : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X'}
    {Gd : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X'}
    (ae : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ Ge)
    (ae' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ Ge')
    (ad : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e' ≫ h) ⊣ Gd) :
    etaleHorizontalDoubleCounitIso A sq N adj adj' =
      Functor.isoWhiskerLeft G
        (conjugateIsoEquiv ae'
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance)
          (etaleCanonicalCompactSupportComparison A e' N).symm).symm ≪≫
      (conjugateIsoEquiv ad (ae'.comp adj)
        (unboundedEtaleLowerShriekCompIso A e' h)).symm ≪≫
      conjugateIsoEquiv ad (adj'.comp ae)
        (unboundedEtaleLowerShriekCompIso A h' e ≪≫
          (unboundedEtaleLowerShriekCongr A sq.toCommSq.w).symm) ≪≫
      Functor.isoWhiskerRight
        (conjugateIsoEquiv ae
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance)
          (etaleCanonicalCompactSupportComparison A e N).symm) G' := by
  apply Iso.ext
  simp only [etaleHorizontalDoubleCounitIso, Iso.trans_hom, Iso.symm_hom,
    conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_whiskerRight _ _ adj,
    ← conjugateEquiv_whiskerLeft _ _ adj', conjugateEquiv_comp,
    conjugateEquiv_comp, conjugateEquiv_comp]
  congr 1
  simp only [etaleHorizontalSupportMateDelta, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc]

/-- Equality of natural transformations, making naturality in K explicit.
Source: blueprint co-smooth etale locality Step 1 and Stacks 0037
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: the single-counit identity identifies the two transformations under the
adjunction hom bijection, component by component; injectivity gives equality. -/
theorem etaleHorizontalDoubleCounit_exchange :
    (etaleHorizontalDoubleCounitIso A sq N adj adj').hom =
      etaleHorizontalCounitRightExchange A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) adj adj' := by
  ext K
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (etaleHorizontalDoubleCounit A sq N adj adj' K).2.1.trans
    (mateEquiv_counit adj adj'
      (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A
        (IsPullback.of_iso_pullback sq.toCommSq
          sq.isoPullback sq.hom_fst sq.hom_snd)).inv) K).symm

end Square

end AlgebraicGeometry.Etale
