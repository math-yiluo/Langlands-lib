/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedOpenDifferenceDiagram

/-! # Gluing derived complexes and compatible morphisms on two opens

Source: literature/stacks-project/cohomology.tex, Tag 08DG (Lemma 20.45.1)
(blueprint: lem-sc-derived-open-gluing-objects).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem isIso_fiber_projection
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) (A : C) (p : T.obj₂ ⟶ A)
    [HasBinaryBiproduct A T.obj₃] (hpIso : IsIso (biprod.lift p T.mor₂)) : IsIso (T.mor₁ ≫ p) := by
  let _ := hpIso
  let T' := Pretriangulated.binaryBiproductTriangle A T.obj₃
  have hT' : T' ∈ distTriang C := Pretriangulated.binaryBiproductTriangle_distinguished _ _
  obtain ⟨a, ha, ha'⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    T T' hT hT' (biprod.lift p T.mor₂) (𝟙 _) (by
      simpa only [T', Pretriangulated.binaryBiproductTriangle,
        Pretriangulated.Triangle.mk, Category.comp_id]
      using (biprod.lift_snd p T.mor₂).symm)
  let φ : T ⟶ T' :=
    { hom₁ := a
      hom₂ := biprod.lift p T.mor₂
      hom₃ := 𝟙 _
      comm₁ := ha
      comm₂ := by
        simpa only [T', Pretriangulated.binaryBiproductTriangle,
          Pretriangulated.Triangle.mk, Category.comp_id]
          using (biprod.lift_snd p T.mor₂).symm
      comm₃ := ha' }
  have hi : IsIso a := Pretriangulated.isIso₁_of_isIso₂₃ φ hT hT' (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  have hp : T.mor₁ ≫ p = a := by
    have he := congrArg (fun z ↦ z ≫ biprod.fst) ha
    simpa [T', Category.assoc] using he
  rw [hp]
  exact hi

private theorem compatible_of_difference
    {C C₁ C₂ C₃ : Type*} [Category C] [Category C₁] [Category C₂] [Category C₃]
    [HasZeroMorphisms C] [Preadditive C₃]
    (rU : C ⥤ C₁) (rV : C ⥤ C₂) (rW : C ⥤ C₃)
    (sU : C₁ ⥤ C₃) (sV : C₂ ⥤ C₃) [rW.PreservesZeroMorphisms]
    (eU : rU ⋙ sU ≅ rW) (eV : rV ⋙ sV ≅ rW)
    {A : C₁} {B : C₂} (c : sU.obj A ≅ sV.obj B)
    {F E D : C} (f : F ⟶ E) (d : E ⟶ D)
    (pU : rU.obj E ⟶ A) (pV : rV.obj E ⟶ B) (k : rW.obj D ⟶ sV.obj B)
    (hz : f ≫ d = 0)
    (hdiff : eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV =
      rW.map d ≫ k) :
    eU.inv.app F ≫ sU.map (rU.map f ≫ pU) ≫ c.hom =
      eV.inv.app F ≫ sV.map (rV.map f ≫ pV) := by
  have hzero : rW.map f ≫ rW.map d ≫ k = 0 := by
    rw [← Category.assoc, ← rW.map_comp, hz, rW.map_zero, zero_comp]
  have he := congrArg (fun z ↦ rW.map f ≫ z) hdiff
  rw [Preadditive.comp_sub, hzero] at he
  have hnU := eU.inv.naturality f
  have hnV := eV.inv.naturality f
  change rW.map f ≫ eU.inv.app E = eU.inv.app F ≫ sU.map (rU.map f) at hnU
  change rW.map f ≫ eV.inv.app E = eV.inv.app F ≫ sV.map (rV.map f) at hnV
  simp only [← Category.assoc] at he
  rw [hnU, hnV] at he
  simpa only [Functor.map_comp, Category.assoc] using sub_eq_zero.mp he

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
-- Additivity of the three-fold composite restriction functors exceeds the default size.
set_option maxHeartbeats 800000 in
-- Elaborating the restriction functors and their comparison isomorphisms needs this budget.
/-- Objects of the derived category glue across a two-open cover with their prescribed
transition, without an assertion about morphisms into another object.
Source: Stacks Project, Cohomology, Tag 08DG, first assertion and cone construction
(blueprint: lem-sc-derived-open-gluing-objects).
Proof: let W = U ∩ V. Form the difference of the two restriction maps from
Rj_U A ⊕ Rj_V B to Rj_W (B|W), using c on the first summand. Complete this
map to a distinguished triangle with first object F. Restrict the triangle to U.
Tag 08FE identifies the other two pushforwards with the same Rj from W to U;
the second component of the map is minus the identity. The resulting split
triangle identifies F|U with A. Interchanging U and V gives F|V ≅ B.
Restrict both projections to W: the kernel equation for the difference map
identifies their transition with c. The displayed canonical comparisons include
the units of the open-subscheme equivalences, so this equation is exactly the
one in the conclusion. The construction also works if an open or W is empty. -/
theorem derived_open_gluing_objects
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.obj A ≅
      (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.obj B) :
    ∃ (F : schemeDerivedCategory X)
      (iU : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj F ≅ A)
      (iV : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V)).mapDerivedCategory.obj F ≅ B),
      ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).inv.app F ≫
        (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map iU.hom ≫ c.hom =
      ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv V).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).inv.app F ≫
        (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map iV.hom := by
  classical
  let rU := (schemeOpenRestriction X U).mapDerivedCategory
  let rV := (schemeOpenRestriction X V).mapDerivedCategory
  let sU := (schemeOpenOverlapRestriction X (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory
  let sV := (schemeOpenOverlapRestriction X (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory
  let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory
  let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U)
  let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V)
  change ∃ (F : schemeDerivedCategory X) (iU : rU.obj F ≅ A) (iV : rV.obj F ≅ B),
    eU.inv.app F ≫ sU.map iU.hom ≫ c.hom = eV.inv.app F ≫ sV.map iV.hom
  let E := (schemeDerivedDirectImage U.ι).obj A ⊞ (schemeDerivedDirectImage V.ι).obj B
  let D := (schemeDerivedDirectImage (U ⊓ V).ι).obj (sV.obj B)
  obtain ⟨d, pU, pV, k, hU, hV, hdiff⟩ :=
    derived_open_difference_diagram.{u, w} X U V hcover A B c
  obtain ⟨F, f, h, ht⟩ := Pretriangulated.distinguished_cocone_triangle₁
    (C := schemeDerivedCategory X) (Y := E) (Z := D) d
  let T : Pretriangulated.Triangle (schemeDerivedCategory X) := Pretriangulated.Triangle.mk f d h
  have ht' : T ∈ distTriang (schemeDerivedCategory X) := ht
  have hiU : IsIso (rU.map f ≫ pU) :=
    isIso_fiber_projection (rU.mapTriangle.obj T) (rU.map_distinguished T ht') A pU (by
      dsimp only [Functor.mapTriangle, T, Pretriangulated.Triangle.mk]
      exact hU)
  have hiV : IsIso (rV.map f ≫ pV) :=
    isIso_fiber_projection (rV.mapTriangle.obj T) (rV.map_distinguished T ht') B pV (by
      dsimp only [Functor.mapTriangle, T, Pretriangulated.Triangle.mk]
      exact hV)
  let _ := hiU
  let _ := hiV
  refine ⟨F, asIso (rU.map f ≫ pU), asIso (rV.map f ≫ pV), ?_⟩
  change eU.inv.app F ≫ sU.map (rU.map f ≫ pU) ≫ c.hom =
    eV.inv.app F ≫ sV.map (rV.map f ≫ pV)
  have hz : f ≫ d = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T ht'
  change eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV =
    rW.map d ≫ k at hdiff
  exact compatible_of_difference rU rV rW sU sV eU eV c f d pU pV k hz hdiff

end AlgebraicGeometry
