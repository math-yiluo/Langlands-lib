/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.FixSiteOpenExchangeSheaf
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Site comparison for cartesian open base change

Source: Stacks Project, Tags 09AF and 0F7B.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

namespace BetaSiteTransportProof

set_option backward.defeqAttrib.useBackward true

/-- The canonical pullback comparison, expressed using localization restriction on both
sites. The first factor converts etale restriction to inverse image; the middle factor
is the recorded canonical comparison, and the last converts pro-etale inverse image to
restriction. No independent comparison is chosen.
Source: Stacks Project, Tags 099R and 09AF
(blueprint: lem-sf-open-comparison-unit-normalization). -/
private noncomputable def openComparisonRestrictionIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j ≪≫
      Functor.isoWhiskerLeft _
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)

set_option backward.defeqAttrib.useBackward true in
private lemma openComparisonRestrictionIso_conjugate
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
        (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j))
      ((Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) U))
      (openComparisonRestrictionIso A j).hom =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  let B := ModuleCat.{u + 1} A
  let r₀ := Etale.upperStarLowerStarAdjunction B j
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s₀ := upperStarLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  change conjugateEquiv (cX.comp s) (r.comp cU)
    (Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction B j).inv _ ≫
      (supportSiteComparisonCoefficientPullbackIso B j).hom ≫
        Functor.whiskerLeft (comparisonUpperStar B X)
          (upperStarIsoOpenImmersionRestriction B j).hom) = _
  rw [← conjugateEquiv_comp (cX.comp s) (r₀.comp cU) (r.comp cU),
    ← conjugateEquiv_comp (cX.comp s) (cX.comp s₀) (r₀.comp cU),
    conjugateEquiv_whiskerLeft s s₀ cX
      (upperStarIsoOpenImmersionRestriction B j).hom,
    conjugateEquiv_whiskerRight r₀ r cU
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv]
  have he : conjugateEquiv r₀ r
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have hp : conjugateEquiv s s₀
      (upperStarIsoOpenImmersionRestriction B j).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [he, hp]
  change (𝟙 _ ≫ (conjugateEquiv (cX.comp s₀) (r₀.comp cU))
    (supportSiteComparisonCoefficientPullbackIso B j).hom) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  exact congrArg Iso.inv
    ((conjugateIsoEquiv (r₀.comp cU) (cX.comp s₀)).apply_symm_apply
      (supportSiteComparisonCoefficientDirectImageIso B j).symm)

set_option backward.defeqAttrib.useBackward true in
private lemma openComparisonRestriction_directImage_mate
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom)
      ) =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  ext M : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]
  change M.obj.map _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ M.obj.map _)) =
    𝟙 _ ≫ M.obj.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply Limits.pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, Scheme.toProEt,
      supportSiteComparisonSiteBaseChangeIso]
  rfl

-- The Tag 09AF comparison preserves the open adjunction units for every ring.
private theorem openComparison_unit (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
          ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app F) ≫
        (openComparisonRestrictionIso A j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
          ((openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} A) j).hom.app F) =
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) := by
  let B := ModuleCat.{u + 1} A
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  let e := Etale.openImmersionLowerShriekAdjunction B j
  let d := openImmersionLowerShriekAdjunction B j
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let α := TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso A j).hom
  let β := TwoSquare.mk _ _ _ _
    (openImmersionLowerShriekComparisonUpperStarIso B j).inv
  let θ := TwoSquare.mk _ _ _ _ (comparisonLowerStarOpenImmersionRestrictionIso B j).hom
  have ha : mateEquiv cX cU α = θ := by
    apply (mateEquiv s r).injective
    change (mateEquiv s r (mateEquiv cX cU α)) =
      (mateEquiv s r θ)
    rw [iterated_mateEquiv_conjugateEquiv]
    exact (openComparisonRestrictionIso_conjugate A j).trans
      (openComparisonRestriction_directImage_mate A j).symm
  have hb : mateEquiv cX cU (mateEquiv e d β) = θ := by
    rw [iterated_mateEquiv_conjugateEquiv]
    exact congrArg Iso.hom
      ((conjugateIsoEquiv (e.comp cX) (cU.comp d)).apply_symm_apply
        (comparisonLowerStarOpenImmersionRestrictionIso B j))
  have h : mateEquiv e d β = α := (mateEquiv cX cU).injective (hb.trans ha.symm)
  have hu := unit_mateEquiv e d β F
  rw [h] at hu
  change (comparisonUpperStar B U).map (e.unit.app F) ≫
    (openComparisonRestrictionIso A j).hom.app _ =
      d.unit.app _ ≫ (openImmersionRestriction B j).map
        ((openImmersionLowerShriekComparisonUpperStarIso B j).inv.app F) at hu
  rw [reassoc_of% hu, ← Functor.map_comp]
  simp
  rfl

private theorem comparison_pullback_eq (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm := by
  have hs : supportSiteComparisonSiteBaseChangeIso j = toProEtCompOverPullbackIso j := by
    ext W
    rfl
  unfold supportSiteComparisonCoefficientPullbackIso comparisonUpperStarCompUpperStarIso
  unfold supportSiteComparisonCoefficientDirectImageIso lowerStarCompComparisonLowerStarIso
  rw [hs]
  rfl

private theorem comparison_open_inverse_unit
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).inv.app F) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
        ((Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app F) ≫
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) := by
  let A := ModuleCat.{u + 1} Λ
  apply transport_open_unit (comparisonUpperStar A U) (comparisonUpperStar A X)
    (Etale.openImmersionLowerShriekAdjunction A j)
    (openImmersionLowerShriekAdjunction A j)
    (Etale.upperStarIsoOpenImmersionRestriction A j)
    (upperStarIsoOpenImmersionRestriction A j)
    (openImmersionLowerShriekComparisonUpperStarIso A j)
    (comparisonUpperStarCompUpperStarIso A j) F
  have h := openComparison_unit Λ j F
  unfold openComparisonRestrictionIso at h
  rw [comparison_pullback_eq] at h
  dsimp only [A] at *
  simpa only [supportSiteComparisonCoefficientPullback, comparisonUpperStar,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc] using h

private local instance etaleFamily (Λ : Type (u + 1)) [CommRing Λ] :
    ∀ T : Scheme.{u}, HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  fun _T ↦ inferInstance

private local instance proetaleFamily (Λ : Type (u + 1)) [CommRing Λ] :
    ∀ T : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) :=
  fun _T ↦ inferInstance

private theorem comparison_coefficient_pullback_eq
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    comparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm := by
  rfl

private theorem etale_comp_transport (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : h = f ≫ g) :
    Etale.upperStarComp (ModuleCat.{u + 1} Λ) f g h w =
      eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) w) ≪≫
        etaleComparisonComp (ModuleCat.{u + 1} Λ) f g := by
  subst w
  simp only [eqToIso_refl]
  rfl

private theorem comparison_etale_square (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} (sq : ChosenCartesianSquare gU j' j g) :
    etaleComparisonSquare (ModuleCat.{u + 1} Λ) sq =
      Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq := by
  have hc : etaleComparisonComp (ModuleCat.{u + 1} Λ) gU j =
      Etale.upperStarComp (ModuleCat.{u + 1} Λ) gU j := by
    unfold etaleComparisonComp Etale.upperStarComp
    rfl
  have he {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (w : f = g) :
      eqToIso (congrArg (etaleComparisonPullback (ModuleCat.{u + 1} Λ))
        w.symm) = (eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) w)).symm := by
    subst w
    rfl
  rw [Etale.squareUpperStarIso, etale_comp_transport]
  unfold etaleComparisonSquare
  rw [hc, he sq.w]
  exact (Iso.trans_assoc _ _ _).symm.trans
    (congrArg (fun e ↦ e ≪≫ Etale.upperStarComp (ModuleCat.{u + 1} Λ) gU j)
      (Iso.trans_symm _ _)).symm

private theorem comparison_pro_square_reverse (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} (sq : ChosenCartesianSquare gU j' j g)
    (sq' : ChosenCartesianSquare j' gU g j) :
    proEtaleComparisonSquare (ModuleCat.{u + 1} Λ) sq' =
      upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w := by
  have hc {Y Z T : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ T) :
      proEtaleComparisonComp (ModuleCat.{u + 1} Λ) f g =
        upperStarComp (ModuleCat.{u + 1} Λ) f g := by
    unfold proEtaleComparisonComp upperStarComp
    rfl
  have he {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (w : f = g) :
      eqToIso (congrArg (proEtaleComparisonPullback (ModuleCat.{u + 1} Λ))
        w) = upperStarCongr (ModuleCat.{u + 1} Λ) w := by
    subst w
    rfl
  simp only [proEtaleComparisonSquare, upperStarCompIso, hc]
  rw [he sq'.w.symm]

private theorem comparison_square_data_flip_eq
    (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} (sq : ChosenCartesianSquare gU j' j g)
    (sq' : ChosenCartesianSquare j' gU g j) :
    let A := ModuleCat.{u + 1} Λ
    comparisonSquareData A j' gU g j sq' =
      ({ L₁ := Etale.upperStar A j
         L₂ := Etale.upperStar A gU
         L₁' := Etale.upperStar A g
         L₂' := Etale.upperStar A j'
         K₀ := comparisonUpperStar A X
         K₁ := comparisonUpperStar A U
         K₁' := comparisonUpperStar A X'
         K₂ := comparisonUpperStar A U'
         R₁ := upperStar A j
         R₂ := upperStar A gU
         R₁' := upperStar A g
         R₂' := upperStar A j'
         c₂ := (comparisonUpperStarCompUpperStarIso A gU).symm
         c₁ := (comparisonUpperStarCompUpperStarIso A j).symm
         c₂' := (comparisonUpperStarCompUpperStarIso A j').symm
         c₁' := (comparisonUpperStarCompUpperStarIso A g).symm
         se := Etale.squareUpperStarIso A sq'.toCommSq
         sp := upperStarCompIso A sq.w } : ComparisonSquareData _ _ _ _ _ _ _ _) := by
  dsimp only
  simp only [comparisonSquareData, comparison_coefficient_pullback_eq Λ,
    comparison_etale_square Λ, comparison_pro_square_reverse Λ sq sq']
  simp only [comparisonCoefficientPullback, etaleComparisonPullback,
    proEtaleComparisonPullback, comparisonUpperStar, Etale.upperStar, upperStar,
    Scheme.smallEtaleTopology]

private theorem component_unpack
    {A B B' C P Q Q' R : Type*} [Category A] [Category B] [Category B']
    [Category C] [Category P] [Category Q] [Category Q'] [Category R]
    (L₁ : A ⥤ B) (L₂ : B ⥤ C) (L₁' : A ⥤ B') (L₂' : B' ⥤ C)
    (K₀ : A ⥤ P) (K₁ : B ⥤ Q) (K₁' : B' ⥤ Q') (K₂ : C ⥤ R)
    (R₁ : P ⥤ Q) (R₂ : Q ⥤ R) (R₁' : P ⥤ Q') (R₂' : Q' ⥤ R)
    (c₂ : K₁ ⋙ R₂ ≅ L₂ ⋙ K₂) (c₁ : K₀ ⋙ R₁ ≅ L₁ ⋙ K₁)
    (c₂' : K₁' ⋙ R₂' ≅ L₂' ⋙ K₂) (c₁' : K₀ ⋙ R₁' ≅ L₁' ⋙ K₁')
    (se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂') (sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂')
    (F : A) (h : ComparisonSquareComponent
      { L₁ := L₁, L₂ := L₂, L₁' := L₁', L₂' := L₂', K₀ := K₀,
        K₁ := K₁, K₁' := K₁', K₂ := K₂, R₁ := R₁, R₂ := R₂,
        R₁' := R₁', R₂' := R₂', c₂ := c₂.symm, c₁ := c₁.symm,
        c₂' := c₂'.symm, c₁' := c₁'.symm, se := se, sp := sp } F) :
    c₂.inv.app (L₁.obj F) ≫ R₂.map (c₁.inv.app F) ≫ sp.hom.app (K₀.obj F) =
      K₂.map (se.hom.app F) ≫ c₂'.inv.app (L₁'.obj F) ≫ R₂'.map (c₁'.inv.app F) := h

/-- Specialized inverse-image comparison square used by the open exchange calculation.
Source: canonical comparison-square coherence, Stacks Tags 099R and 0B65.
(blueprint: lem-fix-site-open-exchange-square).

Proof: flip the chosen Cartesian square using the pullback symmetry isomorphism.
The component equation for this flipped square has exactly the required orientation.
Its pro-etale square is the original inverse-image square, and its coefficient
comparisons are the inverses of the specified pullback comparisons. Normalize the
bundled square data and unpack its component equation. No open-immersion assumption
is needed; the construction also covers empty schemes and the zero coefficient ring. -/
private theorem fixSiteOpenExchangeSquare (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} (sq : ChosenCartesianSquare gU j' j g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) gU).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) gU).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).inv.app F) ≫
      (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U').map
        ((Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).hom.app F) ≫
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j').inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j').map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).inv.app F) := by
  let sq' : ChosenCartesianSquare j' gU g j :=
    { toCommSq := sq.toCommSq.flip
      isoPullback := sq.isoPullback ≪≫ pullbackSymmetry j g
      hom_fst := by simp [sq.hom_snd]
      hom_snd := by simp [sq.hom_fst] }
  have hc := comparison_square_component_of_commRing Λ sq' F
  rw [comparison_square_data_flip_eq Λ sq sq'] at hc
  exact component_unpack _ _ _ _ _ _ _ _ _ _ _ _
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) gU)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j')
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g)
    (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq.flip)
    (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w) F hc

-- Keep the Kan-extension constructions closed while checking the mate calculation.
attribute [local irreducible] upperStar Etale.upperStar openImmersionLowerShriek
  Etale.openImmersionLowerShriek comparisonUpperStar

private theorem pro_open_unit (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq gU j' j g)
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) gU).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j').map
        ((openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) =
    (upperStar (ModuleCat.{u + 1} Λ) gU).map
        ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app F) ≫
      (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) := by
  exact exchange_mate_unit
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j')
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU)
    (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w).hom
    (ProEtale.baseChangeMap (ModuleCat.{u + 1} Λ) sq)
    (pro_baseChange_eq_mate Λ sq) F

private theorem pro_iso_unit (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (hsq : IsPullback gU j' j g)
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) gU).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j').map
        ((openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).hom.app F) =
    (upperStar (ModuleCat.{u + 1} Λ) gU).map
        ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app F) ≫
      (upperStarCompIso (ModuleCat.{u + 1} Λ) hsq.w).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) := by
  exact pro_open_unit Λ hsq.toCommSq F

attribute [local irreducible] openImmersionLowerShriekBaseChangeMap

private theorem beta_forward_comparison (Λ : Type (u + 1)) [CommRing Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare gU j' j g)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) g).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).hom.app F) ≫
      (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) gU).hom.app F) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj F) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').map
        ((@asIso _ _ _ _ _ (Etale.isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} Λ)
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst
            sq.hom_snd))).inv.app F) ≫
    (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j').hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) gU).obj F) := by
  have hsq : IsPullback gU j' j g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  exact exchange_comparison
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) j)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) j')
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) (upperStar (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j') (upperStar (ModuleCat.{u + 1} Λ) j')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g) (Etale.upperStar (ModuleCat.{u + 1} Λ) gU)
    (upperStar (ModuleCat.{u + 1} Λ) g) (upperStar (ModuleCat.{u + 1} Λ) gU)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U) (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X') (comparisonUpperStar (ModuleCat.{u + 1} Λ) U')
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j')
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j')
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j')
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) gU)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j')
    (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).symm
    (@asIso _ _ _ _
      (Etale.openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)
      (Etale.isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) hsq))
    (upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w)
    (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq.flip)
    (comparison_open_inverse_unit Λ j) (comparison_open_inverse_unit Λ j')
    (fun E ↦ by
      have hu := pro_iso_unit Λ hsq E
      have hw : upperStarCompIso (ModuleCat.{u + 1} Λ) hsq.w =
          upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w :=
        congrArg (upperStarCompIso (ModuleCat.{u + 1} Λ)) (Subsingleton.elim _ _)
      rw [hw] at hu
      exact hu)
    (fun E ↦ by
      simpa only [asIso_hom] using
        Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app
          (ModuleCat.{u + 1} Λ) sq.toCommSq E)
    (fixSiteOpenExchangeSquare Λ sq.toChosenCartesianSquare) F

end BetaSiteTransportProof

/-- Site comparison preserves the inverse cartesian open base-change map.
Source: Stacks Project, proetale.tex, lemma-jshriek-comparison (Tag 09AF);
open-unit transpose calculation in step 1 of
lem-cbc-finite-clopen-alpha-site-transport
(blueprint: lem-cbc-finite-clopen-beta-site-transport).

Proof: transpose the forward base-change maps under extension by zero along
b = W ×_T S → W. The transpose is pullback along q of the open unit along i,
followed by the cartesian inverse-image compositor. The pullback comparison
preserves that compositor. The open comparison is the adjunction comparison,
so its unit equation identifies the two open units. The transposes therefore
agree, and injectivity of the adjunction bijection identifies the forward maps.
All four comparison maps and the cartesian base-change maps are isomorphisms;
compose with their inverses to obtain the stated equation. This works also for
an empty open, and uses no properness or finiteness condition on p. -/
theorem finiteClopenBetaSiteTransport
    (Λ : Type (u + 1)) [CommRing Λ]
    {W S T : Scheme.{u}} (i : S ⟶ T) (p : W ⟶ T) [IsOpenImmersion i]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
        ((@asIso _ _ _ _ _ (Etale.isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv.app F) ≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ)
        (pullback.fst p i)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i)).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ)
          (pullback.snd p i)).inv.app F) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) i).hom.app F) ≫
      (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback p i).flip).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj F) := by
  let sq := (IsPullback.of_hasPullback p i).flip
  let osq : OpenImmersionSquare (pullback.snd p i) (pullback.fst p i) i p :=
    { toChosenCartesianSquare :=
        { toCommSq := sq.toCommSq
          isoPullback := sq.isoPullback
          hom_fst := sq.isoPullback_hom_fst
          hom_snd := sq.isoPullback_hom_snd }
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  have h := BetaSiteTransportProof.beta_forward_comparison Λ osq F
  apply (cancel_epi ((comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) p).hom.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj F))).mp
  have hc := congrArg
    (fun f ↦ f ≫ (openImmersionLowerShriek
      (ModuleCat.{u + 1} Λ) (pullback.fst p i)).map
        ((comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} Λ) (pullback.snd p i)).inv.app F)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hc
  dsimp only [Functor.comp_obj] at hc
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hc.symm

end AlgebraicGeometry.ProEtale
