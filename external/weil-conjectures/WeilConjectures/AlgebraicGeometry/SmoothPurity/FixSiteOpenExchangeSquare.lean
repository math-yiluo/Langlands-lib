/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleChartComparison.EtaleChartComparisonIsos
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! Specialized comparison square for the site-comparison open exchange. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

local instance etaleFamily (Λ : Type (u + 1)) [CommRing Λ] :
    ∀ T : Scheme.{u}, HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  fun _T ↦ inferInstance

private theorem comparison_coefficient_pullback_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
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
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
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
theorem fixSiteOpenExchangeSquare (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
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

end AlgebraicGeometry.ProEtale
