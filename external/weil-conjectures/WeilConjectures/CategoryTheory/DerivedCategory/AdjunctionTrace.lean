/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTransAdditive
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

import all Mathlib.Algebra.Homology.Localization

/-!
# Traces of derived adjunctions of exact functors

Let `adj : f ⊣ g` be an adjunction of exact functors between abelian categories, and let
`t : f ⋙ g ⟶ 𝟭` be a *trace* with `u ≫ t = d • 𝟙` for the unit `u`, and `ρ i : f ⋙ g ⟶ f ⋙ g`
finitely many natural transformations with `t ≫ u = ∑ i, ρ i`. Then the derived adjunction
`Lf ⊣ Rg` (`CategoryTheory.Adjunction.derivedAdjunction`) carries a trace and endomorphisms
satisfying the same identities (`CategoryTheory.Adjunction.unit_comp_derivedTrace`,
`CategoryTheory.Adjunction.derivedTrace_comp_unit`).

The unit of the levelwise derived adjunction `D(f) ⊣ D(g)` is the levelwise unit
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_eq`), and the derived adjunction
differs from it by the isomorphisms `Lf ≅ D(f)`, `Rg ≅ D(g)`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The unit of the levelwise derived adjunction `D(f) ⊣ D(g)` is the levelwise unit. -/
lemma mapDerivedCategoryAdjunction_unit_eq :
    adj.mapDerivedCategoryAdjunction.unit =
      (Functor.mapDerivedCategoryIdIso C).inv ≫ Functor.mapDerivedCategoryNatTrans adj.unit ≫
        (Functor.mapDerivedCategoryCompIso f g).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun Y ↦ ?_
  have hu := adj.mapDerivedCategoryAdjunction_unit_app_Qh_obj
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y)
  rw [mapHomotopyCategory_unit_app_quotient] at hu
  have hc := Functor.mapDerivedCategoryCompIso_fac f g Y
  have hn := Functor.mapDerivedCategoryNatTrans_fac adj.unit Y
  have hu' : adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj Y) ≫
      g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.hom.app Y) ≫
        g.mapDerivedCategoryFactors.hom.app ((f.mapHomologicalComplex _).obj Y) =
      DerivedCategory.Q.map ((mapHomologicalComplex (ComplexShape.up ℤ) adj).unit.app Y) := by
    have e1 : (DerivedCategory.quotientCompQhIso C).hom.app Y = 𝟙 _ := rfl
    have e2 : (DerivedCategory.quotientCompQhIso D).inv.app ((f.mapHomologicalComplex _).obj Y) =
      𝟙 _ := rfl
    have e3 : (f.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app Y = 𝟙 _ := rfl
    have e4 := g.mapDerivedCategoryFactorsh_hom_app ((f.mapHomologicalComplex _).obj Y)
    have e5 : (DerivedCategory.quotientCompQhIso D).hom.app ((f.mapHomologicalComplex _).obj Y) =
      𝟙 _ := rfl
    have e6 : (DerivedCategory.quotientCompQhIso C).inv.app ((g.mapHomologicalComplex _).obj
      ((f.mapHomologicalComplex _).obj Y)) = 𝟙 _ := rfl
    have e7 : (g.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((f.mapHomologicalComplex _).obj Y) = 𝟙 _ := rfl
    simp only [e5, e6, e7, Functor.map_id, id_comp] at e4
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app, e1, e2, e3, Functor.map_id,
      id_comp] at hu
    erw [e4] at hu
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_id, comp_id] at hu
    exact hu
  have hi' := Functor.mapDerivedCategoryIdIso_hom_app Y
  rw [← cancel_mono (g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.hom.app Y) ≫
    g.mapDerivedCategoryFactors.hom.app ((f.mapHomologicalComplex _).obj Y) ≫
    DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (f ⋙ g))
      (ComplexShape.up ℤ)).hom.app Y)), reassoc_of% hu']
  simp only [NatTrans.comp_app, assoc]
  rw [hc, hn, ← cancel_epi ((Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj Y)),
    Iso.hom_inv_id_app_assoc, hi', assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  ext n
  simp only [Functor.id_obj, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f,
    mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, id_comp, NatTrans.mapHomologicalComplex_app_f]
  exact comp_id _


variable {ι : Type*} [Fintype ι]

/-- The trace `D(f) ⋙ D(g) ⟶ 𝟭` induced by a trace `t : f ⋙ g ⟶ 𝟭`. -/
noncomputable def mapDerivedCategoryTrace (t : f ⋙ g ⟶ 𝟭 C) :
    f.mapDerivedCategory ⋙ g.mapDerivedCategory ⟶ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso f g).hom ≫ Functor.mapDerivedCategoryNatTrans t ≫
    (Functor.mapDerivedCategoryIdIso C).hom

/-- The endomorphism of `D(f) ⋙ D(g)` induced by an endomorphism of `f ⋙ g`. -/
noncomputable def mapDerivedCategoryEndo (σ : f ⋙ g ⟶ f ⋙ g) :
    f.mapDerivedCategory ⋙ g.mapDerivedCategory ⟶ f.mapDerivedCategory ⋙ g.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso f g).hom ≫ Functor.mapDerivedCategoryNatTrans σ ≫
    (Functor.mapDerivedCategoryCompIso f g).inv

lemma mapDerivedCategoryAdjunction_unit_comp_mapDerivedCategoryTrace {t : f ⋙ g ⟶ 𝟭 C} {d : ℕ}
    (hd : adj.unit ≫ t = d • 𝟙 _) :
    adj.mapDerivedCategoryAdjunction.unit ≫ mapDerivedCategoryTrace t = d • 𝟙 _ := by
  rw [mapDerivedCategoryAdjunction_unit_eq, mapDerivedCategoryTrace, assoc, assoc,
    Iso.inv_hom_id_assoc, ← Functor.mapDerivedCategoryNatTrans_comp_assoc, hd,
    Functor.mapDerivedCategoryNatTrans_nsmul, Functor.mapDerivedCategoryNatTrans_id,
    Preadditive.nsmul_comp, id_comp, Preadditive.comp_nsmul, Iso.inv_hom_id]

lemma mapDerivedCategoryTrace_comp_mapDerivedCategoryAdjunction_unit {t : f ⋙ g ⟶ 𝟭 C}
    {ρ : ι → (f ⋙ g ⟶ f ⋙ g)} (ht : t ≫ adj.unit = ∑ i, ρ i) :
    mapDerivedCategoryTrace t ≫ adj.mapDerivedCategoryAdjunction.unit =
      ∑ i, mapDerivedCategoryEndo (ρ i) := by
  rw [mapDerivedCategoryAdjunction_unit_eq, mapDerivedCategoryTrace, assoc, assoc,
    Iso.hom_inv_id_assoc, ← Functor.mapDerivedCategoryNatTrans_comp_assoc, ht,
    Functor.mapDerivedCategoryNatTrans_sum]
  simp only [mapDerivedCategoryEndo, Preadditive.sum_comp, Preadditive.comp_sum]

/-- The comparison `Lf ⋙ Rg ≅ D(f) ⋙ D(g)` of the derived and levelwise composites. -/
noncomputable def derivedCompIsoMapDerivedCategoryComp :
    f.leftDerivedFunctor ⋙ g.rightDerivedFunctor ≅
      f.mapDerivedCategory ⋙ g.mapDerivedCategory :=
  Functor.isoWhiskerRight f.leftDerivedFunctorIsoMapDerivedCategory g.rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft f.mapDerivedCategory g.rightDerivedFunctorIsoMapDerivedCategory

lemma mapDerivedCategoryAdjunction_unit_eq_derivedAdjunction_unit :
    adj.mapDerivedCategoryAdjunction.unit =
      adj.derivedAdjunction.unit ≫ derivedCompIsoMapDerivedCategoryComp.hom := by
  ext K
  simp [mapDerivedCategoryAdjunction, derivedCompIsoMapDerivedCategoryComp]

/-- **The derived trace**: a trace `t : f ⋙ g ⟶ 𝟭` of an adjunction of exact functors induces a
trace `Lf ⋙ Rg ⟶ 𝟭` of the derived adjunction. -/
noncomputable def derivedTrace (t : f ⋙ g ⟶ 𝟭 C) :
    f.leftDerivedFunctor ⋙ g.rightDerivedFunctor ⟶ 𝟭 _ :=
  derivedCompIsoMapDerivedCategoryComp.hom ≫ mapDerivedCategoryTrace t

/-- The endomorphism of `Lf ⋙ Rg` induced by an endomorphism of `f ⋙ g`. -/
noncomputable def derivedEndo (σ : f ⋙ g ⟶ f ⋙ g) :
    f.leftDerivedFunctor ⋙ g.rightDerivedFunctor ⟶ f.leftDerivedFunctor ⋙ g.rightDerivedFunctor :=
  derivedCompIsoMapDerivedCategoryComp.hom ≫ mapDerivedCategoryEndo σ ≫
    derivedCompIsoMapDerivedCategoryComp.inv

/-- **The derived unit followed by the derived trace is the degree** if `u ≫ t = d • 𝟙`. -/
theorem unit_comp_derivedTrace {t : f ⋙ g ⟶ 𝟭 C} {d : ℕ} (hd : adj.unit ≫ t = d • 𝟙 _) :
    adj.derivedAdjunction.unit ≫ derivedTrace t = d • 𝟙 _ := by
  rw [derivedTrace, ← assoc, ← mapDerivedCategoryAdjunction_unit_eq_derivedAdjunction_unit,
    mapDerivedCategoryAdjunction_unit_comp_mapDerivedCategoryTrace adj hd]

/-- **The derived trace followed by the derived unit is the sum of the derived endomorphisms** if
`t ≫ u = ∑ i, ρ i`. -/
theorem derivedTrace_comp_unit {t : f ⋙ g ⟶ 𝟭 C} {ρ : ι → (f ⋙ g ⟶ f ⋙ g)}
    (ht : t ≫ adj.unit = ∑ i, ρ i) :
    derivedTrace t ≫ adj.derivedAdjunction.unit = ∑ i, derivedEndo (ρ i) := by
  have h : adj.derivedAdjunction.unit =
      adj.mapDerivedCategoryAdjunction.unit ≫ derivedCompIsoMapDerivedCategoryComp.inv := by
    rw [mapDerivedCategoryAdjunction_unit_eq_derivedAdjunction_unit, assoc, Iso.hom_inv_id,
      comp_id]
  rw [h, derivedTrace, assoc, ← assoc (mapDerivedCategoryTrace t),
    mapDerivedCategoryTrace_comp_mapDerivedCategoryAdjunction_unit adj ht]
  simp only [derivedEndo, Preadditive.sum_comp, Preadditive.comp_sum]

end CategoryTheory.Adjunction
