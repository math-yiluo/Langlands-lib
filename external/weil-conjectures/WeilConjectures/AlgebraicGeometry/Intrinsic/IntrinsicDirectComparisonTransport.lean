/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-! Transport of a fixed-scalar mate through the intrinsic realization equivalences. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

noncomputable def sfIntrinsicTransportRight
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁]
    (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {R : C₁ ⥤ C₀} {R' : D₁ ⥤ D₀}
    (b : (f.inverse ⋙ R ⋙ e.functor) ≅ R') :
    R' ⋙ e.inverse ≅ f.inverse ⋙ R :=
  Functor.isoWhiskerRight b.symm e.inverse ≪≫
    Functor.isoWhiskerLeft (f.inverse ⋙ R) e.unitIso.symm

private theorem transportRight_counit
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁]
    (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {R : C₁ ⥤ C₀} {R' : D₁ ⥤ D₀}
    (c : f.functor ⋙ R' ≅ R ⋙ e.functor) (N : D₁) :
    e.counitIso.inv.app (R'.obj N) ≫
        e.functor.map ((sfIntrinsicTransportRight e f (R := R) (R' := R')
          (Functor.isoWhiskerLeft f.inverse c.symm ≪≫
            Functor.isoWhiskerRight f.counitIso R')).hom.app N) =
      R'.map (f.counitIso.inv.app N) ≫ c.hom.app (f.inverse.obj N) := by
  change e.counitIso.inv.app (R'.obj N) ≫
      e.functor.map (e.inverse.map
        (R'.map (f.counitIso.inv.app N) ≫ c.hom.app (f.inverse.obj N)) ≫
        e.unitIso.inv.app (R.obj (f.inverse.obj N))) = _
  have hn := (e.counitIso.inv.naturality
    (R'.map (f.counitIso.inv.app N) ≫ c.hom.app (f.inverse.obj N))).symm
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [Functor.map_comp, ← Category.assoc, hn, Category.assoc,
    e.counitInv_functor_comp, Category.comp_id]

private theorem transportRight_normalized
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁]
    (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {R : C₁ ⥤ C₀} {R' : D₁ ⥤ D₀}
    (c : f.functor ⋙ R' ≅ R ⋙ e.functor) (M : C₁) :
    e.counitIso.inv.app (R'.obj (f.functor.obj M)) ≫
        e.functor.map ((sfIntrinsicTransportRight e f (R := R) (R' := R')
          (Functor.isoWhiskerLeft f.inverse c.symm ≪≫
            Functor.isoWhiskerRight f.counitIso R')).hom.app (f.functor.obj M) ≫
          R.map (f.unitIso.inv.app M)) = c.hom.app M := by
  rw [Functor.map_comp, ← Category.assoc, transportRight_counit, Category.assoc]
  have hn := (c.hom.naturality (f.unitIso.inv.app M)).symm
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  rw [hn]
  rw [← Category.assoc, ← R'.map_comp, f.counitInv_functor_comp]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [R'.map_id, Category.id_comp]

private theorem comparisonTransport
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    {R : C₁ ⥤ C₀} {S : C₂ ⥤ C₁} {T : C₂ ⥤ C₀}
    {R' : D₁ ⥤ D₀} {S' : D₂ ⥤ D₁}
    (c : e₁.functor ⋙ R' ≅ R ⋙ e₀.functor)
    (d : e₂.functor ⋙ S' ≅ S ⋙ e₁.functor)
    (α : S ⋙ R ⟶ T) (M : C₂) :
    R'.map (d.hom.app M) ≫ c.hom.app (S.obj M) ≫ e₀.functor.map (α.app M) =
      e₀.counitIso.inv.app (R'.obj (S'.obj (e₂.functor.obj M))) ≫
        e₀.functor.map
          ((sfIntrinsicTransportRight e₀ e₁ (R := R) (R' := R')
            (Functor.isoWhiskerLeft e₁.inverse c.symm ≪≫
              Functor.isoWhiskerRight e₁.counitIso R')).hom.app
                (S'.obj (e₂.functor.obj M)) ≫
            R.map ((sfIntrinsicTransportRight e₁ e₂ (R := S) (R' := S')
              (Functor.isoWhiskerLeft e₂.inverse d.symm ≪≫
                Functor.isoWhiskerRight e₂.counitIso S')).hom.app (e₂.functor.obj M)) ≫
            α.app (e₂.inverse.obj (e₂.functor.obj M)) ≫
            T.map (e₂.unitIso.inv.app M)) := by
  let r := sfIntrinsicTransportRight e₀ e₁ (R := R) (R' := R')
    (Functor.isoWhiskerLeft e₁.inverse c.symm ≪≫
      Functor.isoWhiskerRight e₁.counitIso R')
  let s := sfIntrinsicTransportRight e₁ e₂ (R := S) (R' := S')
    (Functor.isoWhiskerLeft e₂.inverse d.symm ≪≫
      Functor.isoWhiskerRight e₂.counitIso S')
  let N := e₂.functor.obj M
  let h : e₁.inverse.obj (S'.obj N) ⟶ S.obj M :=
    s.hom.app N ≫ S.map (e₂.unitIso.inv.app M)
  have hd : e₁.counitIso.inv.app (S'.obj N) ≫ e₁.functor.map h = d.hom.app M :=
    transportRight_normalized e₁ e₂ d M
  have hc : e₀.counitIso.inv.app (R'.obj (S'.obj N)) ≫
      e₀.functor.map (r.hom.app (S'.obj N)) =
      R'.map (e₁.counitIso.inv.app (S'.obj N)) ≫
        c.hom.app (e₁.inverse.obj (S'.obj N)) :=
    transportRight_counit e₀ e₁ c (S'.obj N)
  have hn : e₀.functor.map (R.map h) ≫ e₀.functor.map (α.app M) =
      e₀.functor.map (R.map (s.hom.app N) ≫ α.app (e₂.inverse.obj N) ≫
        T.map (e₂.unitIso.inv.app M)) := by
    rw [← e₀.functor.map_comp]
    apply congrArg e₀.functor.map
    dsimp only [h]
    have hn := α.naturality (e₂.unitIso.inv.app M)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
    rw [Functor.map_comp, Category.assoc, hn]
  calc
    _ = (R'.map (e₁.counitIso.inv.app (S'.obj N)) ≫
        c.hom.app (e₁.inverse.obj (S'.obj N))) ≫
        e₀.functor.map (R.map h) ≫ e₀.functor.map (α.app M) := by
      rw [← hd, Functor.map_comp]
      simp only [Category.assoc]
      have hn := c.hom.naturality h
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [← Category.assoc (R'.map (e₁.functor.map h)), hn]
      simp only [Category.assoc]
    _ = (e₀.counitIso.inv.app (R'.obj (S'.obj N)) ≫
        e₀.functor.map (r.hom.app (S'.obj N))) ≫
        e₀.functor.map (R.map h) ≫ e₀.functor.map (α.app M) := by rw [hc]
    _ = _ := by
      simp only [Category.assoc]
      rw [hn, ← e₀.functor.map_comp]

noncomputable def sfIntrinsicAmbientCoordinate
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective]
    (k : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor) :
    (proEtaleConstantDerivedDirectImage g A).obj
        ((proEtaleConstantDerivedDirectImage f A).obj
          ((sfIntrinsicDerivedEquivalence X A).functor.obj (DerivedCategory.Q.obj I))) ⟶
      ((sfIntrinsicDerivedEquivalence Z A).functor.obj
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I))) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let eZ := sfIntrinsicDerivedEquivalence Z A
  let eY := sfIntrinsicDerivedEquivalence Y A
  let eX := sfIntrinsicDerivedEquivalence X A
  let ag0 := derivedUpperStarLowerStarAdjunction B g
  let af0 := derivedUpperStarLowerStarAdjunction B f
  let at0 := derivedUpperStarLowerStarAdjunction B (f ≫ g)
  let bg : (eY.inverse ⋙ (lowerStar B g).rightDerivedFunctor ⋙ eZ.functor) ≅
      proEtaleConstantDerivedDirectImage g A :=
    Functor.isoWhiskerLeft eY.inverse
      (sfIntrinsicDerivedDirectImageComparison g A).symm ≪≫
      Functor.isoWhiskerRight eY.counitIso _
  let bf : (eX.inverse ⋙ (lowerStar B f).rightDerivedFunctor ⋙ eY.functor) ≅
      proEtaleConstantDerivedDirectImage f A :=
    Functor.isoWhiskerLeft eX.inverse
      (sfIntrinsicDerivedDirectImageComparison f A).symm ≪≫
      Functor.isoWhiskerRight eX.counitIso _
  let N := eX.functor.obj (DerivedCategory.Q.obj I)
  let q := (sfIntrinsicTransportRight eZ eY bg).hom.app
      ((proEtaleConstantDerivedDirectImage f A).obj N) ≫
    (lowerStar B g).rightDerivedFunctor.map
      ((sfIntrinsicTransportRight eY eX bf).hom.app N) ≫
    ((conjugateEquiv (ag0.comp af0) at0 k.hom).app (eX.inverse.obj N)) ≫
    (lowerStar B (f ≫ g)).rightDerivedFunctor.map
      (eX.unitIso.inv.app (DerivedCategory.Q.obj I))
  simpa only [Functor.comp_obj, Functor.id_obj, eX, N] using
    (eZ.counitIso.inv.app
      ((proEtaleConstantDerivedDirectImage g A).obj
        ((proEtaleConstantDerivedDirectImage f A).obj N)) ≫ eZ.functor.map q)

/-
The direct-image comparison transport identity.  It is the comparison component of the
mate-pasting calculation, before the fixed-scalar conjugate is specialized.  The parameter
`k` makes this strictly more general than the paper's single compositor instance.

Source: Stacks Tags 03D1 and 0D6E.
-/
theorem sfIntrinsicDirectComparisonTransport
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective]
    (k : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor) :
    (proEtaleConstantDerivedDirectImage g A).map
        ((sfIntrinsicDerivedDirectImageComparison f A).hom.app (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedDirectImageComparison g A).hom.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedEquivalence Z A).functor.map
        ((conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).comp
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f))
          (derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)) k).hom.app
          (DerivedCategory.Q.obj I)) =
      sfIntrinsicAmbientCoordinate A f g I k := by
  exact comparisonTransport
    (sfIntrinsicDerivedEquivalence Z A) (sfIntrinsicDerivedEquivalence Y A)
    (sfIntrinsicDerivedEquivalence X A)
    (sfIntrinsicDerivedDirectImageComparison g A)
    (sfIntrinsicDerivedDirectImageComparison f A)
    (conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).comp
        (derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f))
      (derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)) k.hom)
    (DerivedCategory.Q.obj I)

end AlgebraicGeometry.Scheme
