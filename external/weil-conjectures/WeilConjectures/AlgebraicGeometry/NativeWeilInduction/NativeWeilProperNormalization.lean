/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilInductionComparisonData
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison

/-! # Unit normalization of the native proper comparison

## References

* Stacks Project, Tags 079P, 08BJ and 070Y
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

attribute [instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry.NativeWeilInduction

section

universe v w

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
  [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
  [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra P)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra Q)]

omit [Abelian.HasKInjectiveResolutions (IsoAlgebra Q)] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightForget_unit (e : L ⋙ Q ≅ P ⋙ L)
    (J : HomotopyCategory (IsoAlgebra P) (.up ℤ)) :
    (IsoAlgebra.forget Q).mapDerivedCategory.map
        ((IsoAlgebra.mapOfNatIso e).rightDerivedFunctorUnit.app J) ≫
      (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso P e).hom.app
        (_root_.DerivedCategory.Qh.obj J) ≫
      L.rightDerivedFunctor.map ((IsoAlgebra.forget P).mapDerivedCategoryFactorsh.hom.app J) =
    (IsoAlgebra.forget Q).mapDerivedCategoryFactorsh.hom.app
        (((IsoAlgebra.mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj J) ≫
      L.rightDerivedFunctorUnit.app
        (((IsoAlgebra.forget P).mapHomotopyCategory (.up ℤ)).obj J) := by
  let M := IsoAlgebra.mapOfNatIso e
  let r := IsoAlgebra.forget P
  let s := IsoAlgebra.forget Q
  let a := Functor.rightDerivedFunctorCompMapDerivedCategoryIso M s
  have ha := Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac M s J
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at ha
  have ha' : s.mapDerivedCategory.map (M.rightDerivedFunctorUnit.app J) ≫
      a.inv.app (_root_.DerivedCategory.Qh.obj J) =
      s.mapDerivedCategoryFactorsh.hom.app ((M.mapHomotopyCategory (.up ℤ)).obj J) ≫
        (M ⋙ s).rightDerivedFunctorUnit.app J := by
    rw [← cancel_mono (a.hom.app (_root_.DerivedCategory.Qh.obj J))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [ha]
    simp only [Iso.hom_inv_id_app_assoc]
    exact Category.comp_id _
  dsimp only [IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ha']
  simp only [Category.assoc]
  have hb := Functor.rightDerivedNatTrans_app
    (M ⋙ s).rightDerivedFunctor (r ⋙ L).rightDerivedFunctor
    (M ⋙ s).rightDerivedFunctorUnit (r ⋙ L).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso (IsoAlgebra P) (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (IsoAlgebra.mapOfNatIsoCompForgetIso e).hom (.up ℤ)) _root_.DerivedCategory.Qh) J
  have he : _root_.DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (IsoAlgebra.mapOfNatIsoCompForgetIso e).hom (.up ℤ)).app J) = 𝟙 _ := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
    change _root_.DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (.up ℤ)).map (𝟙 _)) = _
    simp only [CategoryTheory.Functor.map_id]
    rfl
  change (M ⋙ s).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorNatIso
        (IsoAlgebra.mapOfNatIsoCompForgetIso e)).hom.app
        (_root_.DerivedCategory.Qh.obj J) = _ at hb
  dsimp only [Functor.whiskerRight_app] at hb
  erw [he, Category.id_comp] at hb
  rw [reassoc_of% hb]
  have hc : (r ⋙ L).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompIso r L).hom.app
        (_root_.DerivedCategory.Qh.obj J) =
      (Functor.rightDerivedFunctorCompUnit r L).app J := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [reassoc_of% hc]
  have hunit : (Functor.rightDerivedFunctorCompUnit r L).app J =
      L.rightDerivedFunctorUnit.app ((r.mapHomotopyCategory (.up ℤ)).obj J) ≫
        L.rightDerivedFunctor.map (r.rightDerivedFunctorUnit.app J) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
    simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    have hh : (Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ L)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) = 𝟙 _ := rfl
    erw [hh, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hunit]
  simp only [Category.assoc]
  rw [← L.rightDerivedFunctor.map_comp, ← L.rightDerivedFunctor.map_comp]
  have hd := congr_app r.rightDerivedFunctorIsoMapDerivedCategory_hom_fac J
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hd
  have hcancel : r.rightDerivedFunctorUnit.app J ≫
      r.rightDerivedFunctorIsoMapDerivedCategory.hom.app (_root_.DerivedCategory.Qh.obj J) ≫
        r.mapDerivedCategoryFactorsh.hom.app J = 𝟙 _ := by
    rw [← Category.assoc, hd, Iso.inv_hom_id_app]
  erw [hcancel, CategoryTheory.Functor.map_id, Category.comp_id]

end

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The canonical proper comparison respects the actual right-derived units. -/
theorem nativeWeil_proper_normalization
    {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))] (c : Compactification f) :
    ProperNormalization k₀ l f c := by
  intro J hJ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (.of k₀)).geometricFiber) ℤ
  exact rightForget_unit _ _ _ _ ((HomotopyCategory.quotient _ (.up ℤ)).obj J)

end AlgebraicGeometry.NativeWeilInduction
