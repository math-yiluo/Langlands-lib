/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryProductOne
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.TensorShiftNaturality
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Tate orientations from untwisted orientations

Let `a : X ⟶ Y` admit a compactification, `o : Λ_X[2d] ≅ Ra^! Λ_Y` an *untwisted orientation*
and `e : Λ_Y(d) ≅ Λ_Y` a trivialization of the Tate twist on the base (which exists for `Y` the
spectrum of a separably closed field). Then `Λ_X(d) ≅ La^* Λ_Y(d) ≅ La^* Λ_Y ≅ Λ_X`, and `o`
becomes a Tate orientation (`AlgebraicGeometry.Etale.TateOrientation.ofUnit`). This file computes
its twisted and untwisted smooth traces: they are the *unit trace*
`(Ra_! Λ_X)[2d] ≅ Ra_!(Λ_X[2d]) ⟶ Ra_! Ra^! Λ_Y ⟶ Λ_Y` of `o`
(`AlgebraicGeometry.Etale.TateOrientation.unitTrace`), read through `e`.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.twistedSmoothTrace_ofUnit`: the twisted smooth trace
  is `M ⊗ᴸ Λ_Y(d) ≅ M ⊗ᴸ Λ_Y ≅ M ⟶ Λ_Y`, `M = (Ra_! Λ_X)[2d]`, with the unit trace.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace_ofUnit`: the untwisted smooth
  trace is the unit trace followed by an isomorphism `Λ_Y ≅ Λ_Y(-d)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

-- The generic lemmas on the projection map (`AlgebraicGeometry.Etale.projectionMap_rightUnitality`)
-- build the monoidal structure of `D(X_ét, Λ)` from the symmetric structure of `ModuleCat Λ`.
-- Elaborating with the same instances keeps the kernel from unfolding the derived functors to
-- compare the two (defeq) braidings of `ModuleCat Λ`.
attribute [local instance 10000] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.hasFunctorialFlatResolution_sheaf

namespace AlgebraicGeometry.Etale.TateOrientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] {d : ℕ} [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ Y]

variable (a) in
/-- The trivialization `Λ_X(d) ≅ La^* Λ_Y(d) ≅ La^* Λ_Y ≅ Λ_X` induced by a trivialization
`e : Λ_Y(d) ≅ Λ_Y` on the base. -/
noncomputable def tateObjectIsoUnitOfIso (e : tateObject Λ Y d ≅ 𝟙_ _) :
    tateObject Λ X d ≅ 𝟙_ (DerivedCategoryModule Λ X) :=
  (leftDerivedUpperStarTateObjectIso a (d : ℤ)).symm ≪≫
    (L((a)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ leftDerivedUpperStarUnitIso _ a

/-- The Tate orientation `Λ_X(d)[2d] ≅ Λ_X[2d] ≅ Ra^! Λ_Y` of an untwisted orientation
`o : Λ_X[2d] ≅ Ra^! Λ_Y` and a trivialization `e : Λ_Y(d) ≅ Λ_Y`. -/
noncomputable def ofUnit
    (o : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a)
    (e : tateObject Λ Y d ≅ 𝟙_ _) : TateOrientation Λ a d :=
  (shiftFunctor _ (2 * d : ℤ)).mapIso (λ_ (tateObject Λ X d) ≪≫ tateObjectIsoUnitOfIso a e) ≪≫ o

/-- The *unit trace* `(Ra_! Λ_X)[2d] ≅ Ra_!(Λ_X[2d]) ⟶ Ra_! Ra^! Λ_Y ⟶ Λ_Y` of an untwisted
orientation `o : Λ_X[2d] ≅ Ra^! Λ_Y`. -/
noncomputable def unitTrace
    (o : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) :
    ((R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ⟶ 𝟙_ (DerivedCategoryModule Λ Y) :=
  ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫
    (R(a)_![ModuleCat.{u + 1} Λ]).map o.hom ≫
      (rightDerivedUpperShriekAdjunction Λ a).counit.app (𝟙_ _)

lemma dualizingComplexIso_ofUnit_hom
    (o : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a)
    (e : tateObject Λ Y d ≅ 𝟙_ _) :
    (ofUnit o e).dualizingComplexIso.hom =
      (tateObjectIsoUnitOfIso a e).hom⟦(2 * d : ℤ)⟧' ≫ o.hom := by
  simp only [dualizingComplexIso, ofUnit, derivedTensorLeftUnitor, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]

/-- The twisted smooth trace, unfolded. -/
lemma twistedSmoothTrace_eq (γ : TateOrientation Λ a d) :
    γ.twistedSmoothTrace =
      (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (((projectionMap _ a).app (constantComplex Λ X)).app (tateObject Λ Y d))⟦(2 * d : ℤ)⟧' ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
          (leftDerivedUpperStarTateObjectIso a d).hom ≫
            (derivedTensorLeftUnitor _ X _).hom))⟦(2 * d : ℤ)⟧' ≫
          ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫
            (R(a)_![ModuleCat.{u + 1} Λ]).map γ.dualizingComplexIso.hom ≫
              (rightDerivedUpperShriekAdjunction Λ a).counit.app (𝟙_ _) :=
  rfl

omit [Finite Λ] in
variable (a) in
/-- The projection map at `Λ_Y(d)`, followed by `Λ_X ⊗ᴸ La^* Λ_Y(d) ≅ Λ_X(d) ≅ Λ_X`, is the
right unitor read through `e : Λ_Y(d) ≅ Λ_Y`. -/
lemma projectionMap_comp_map_tateObjectIsoUnitOfIso_hom (e : tateObject Λ Y d ≅ 𝟙_ _) :
    ((projectionMap _ a).app (constantComplex Λ X)).app (tateObject Λ Y d) ≫
      (R(a)_![ModuleCat.{u + 1} Λ]).map ((((derivedTensor _ X).obj (constantComplex Λ X)).map
        (leftDerivedUpperStarTateObjectIso a (d : ℤ)).hom ≫ (derivedTensorLeftUnitor _ X _).hom) ≫
          (tateObjectIsoUnitOfIso a e).hom) =
    ((Rf_!(HasCompactification.compactification a)[ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X) ◁
        e.hom) ≫
      (ρ_ ((Rf_!(HasCompactification.compactification a)[ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ X))).hom := by
  have hW : (((derivedTensor _ X).obj (constantComplex Λ X)).map
      (leftDerivedUpperStarTateObjectIso a (d : ℤ)).hom ≫ (derivedTensorLeftUnitor _ X _).hom) ≫
        (tateObjectIsoUnitOfIso a e).hom =
      constantComplex Λ X ◁ (L((a)^*[ModuleCat.{u + 1} Λ])).map e.hom ≫
        (constantComplex Λ X ◁ (leftDerivedUpperStarUnitIso _ a).hom ≫
          (ρ_ (constantComplex Λ X)).hom) := by
    change ((𝟙_ _) ◁ (leftDerivedUpperStarTateObjectIso a (d : ℤ)).hom ≫ (λ_ _).hom) ≫
        (tateObjectIsoUnitOfIso a e).hom =
      (𝟙_ _) ◁ (L((a)^*[ModuleCat.{u + 1} Λ])).map e.hom ≫
        ((𝟙_ _) ◁ (leftDerivedUpperStarUnitIso _ a).hom ≫ (ρ_ _).hom)
    simp only [tateObjectIsoUnitOfIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← unitors_equal]
    simp
  have h := projectionMap_naturality_right (ModuleCat.{u + 1} Λ) a (constantComplex Λ X) e.hom
  simp only [derivedTensor, curriedTensor_obj_map] at h
  rw [hW, Functor.map_comp, ← reassoc_of% h,
    projectionMap_rightUnitality (ModuleCat.{u + 1} Λ) a (constantComplex Λ X)]
  rfl

omit [Finite Λ] [HasInvertibleExponent Λ Y] in
/-- The commutation of `- ⊗ᴸ Λ_Y(d)` with the shifts, read through `e : Λ_Y(d) ≅ Λ_Y`, is the
right unitor. -/
@[reassoc]
lemma commShiftIso_hom_app_comp_shift_map_rightUnitor (e : tateObject Λ Y d ≅ 𝟙_ _)
    (R : DerivedCategoryModule Λ Y) (n : ℤ) :
    (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso n).hom.app R ≫
      ((R ◁ e.hom) ≫ (ρ_ R).hom)⟦n⟧' = (R⟦n⟧ ◁ e.hom) ≫ (ρ_ _).hom := by
  have h1 := derivedTensor_flip_commShiftIso_hom_app_naturality e.hom R n
  have h2 := derivedTensorRightUnitor_commShift R n
  change _ ≫ ((((derivedTensor _ Y).obj R).map e.hom) ≫
      (derivedTensorRightUnitor _ Y R).hom)⟦n⟧' =
    ((derivedTensor _ Y).obj (R⟦n⟧)).map e.hom ≫ (derivedTensorRightUnitor _ Y _).hom
  rw [Functor.map_comp, reassoc_of% h1, h2]

/-- The twisted smooth trace of `AlgebraicGeometry.Etale.TateOrientation.ofUnit` is
`M ⊗ᴸ Λ_Y(d) ≅ M ⊗ᴸ Λ_Y ≅ M ⟶ Λ_Y` with the unit trace, `M = (Ra_! Λ_X)[2d]`. -/
lemma twistedSmoothTrace_ofUnit
    (o : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a)
    (e : tateObject Λ Y d ≅ 𝟙_ _) :
    (ofUnit o e).twistedSmoothTrace =
      (_ ◁ e.hom) ≫ (ρ_ _).hom ≫ unitTrace o := by
  have h1 := Functor.commShiftIso_inv_naturality (R(a)_![ModuleCat.{u + 1} Λ])
    (tateObjectIsoUnitOfIso a e).hom (2 * d : ℤ)
  have h3 : (((projectionMap _ a).app (constantComplex Λ X)).app
      (tateObject Λ Y d))⟦(2 * d : ℤ)⟧' ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj (constantComplex Λ X)).map
        (leftDerivedUpperStarTateObjectIso a (d : ℤ)).hom))⟦(2 * d : ℤ)⟧' ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).map (derivedTensorLeftUnitor _ X _).hom)⟦(2 * d : ℤ)⟧' ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).map (tateObjectIsoUnitOfIso a e).hom)⟦(2 * d : ℤ)⟧' =
      (((Rf_!(HasCompactification.compactification a)[ModuleCat.{u + 1} Λ]).obj
          (constantComplex Λ X) ◁ e.hom) ≫
        (ρ_ ((Rf_!(HasCompactification.compactification a)[ModuleCat.{u + 1} Λ]).obj
          (constantComplex Λ X))).hom)⟦(2 * d : ℤ)⟧' := by
    have := congrArg (fun φ ↦ φ⟦(2 * d : ℤ)⟧')
      (projectionMap_comp_map_tateObjectIsoUnitOfIso_hom a e)
    simpa only [Functor.map_comp, Category.assoc] using this
  rw [twistedSmoothTrace_eq, dualizingComplexIso_ofUnit_hom]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h1, reassoc_of% h3,
    reassoc_of% (commShiftIso_hom_app_comp_shift_map_rightUnitor e
    ((Rf_!(HasCompactification.compactification a)[ModuleCat.{u + 1} Λ]).obj
      (constantComplex Λ X)) (2 * d : ℤ))]
  set_option maxRecDepth 10000 in rfl

/-- The isomorphism `Λ_Y ≅ Λ_Y(d) ⊗ᴸ Λ_Y(-d) ≅ Λ_Y ⊗ᴸ Λ_Y(-d) ≅ Λ_Y(-d)` of a trivialization
`e : Λ_Y(d) ≅ Λ_Y`. -/
noncomputable def unitIsoTateObjectNeg (e : tateObject Λ Y d ≅ 𝟙_ _) :
    𝟙_ (DerivedCategoryModule Λ Y) ≅ tateObject Λ Y (-d) :=
  constantComplexIsoTateObjectTensor Y d ≪≫ whiskerRightIso e _ ≪≫ λ_ _

/-- The untwisted smooth trace, unfolded. -/
lemma untwistedSmoothTrace_eq (γ : TateOrientation Λ a d) :
    γ.untwistedSmoothTrace =
      (ρ_ _).inv ≫ _ ◁ (constantComplexIsoTateObjectTensor Y d).hom ≫ (α_ _ _ _).inv ≫
        γ.twistedSmoothTrace ▷ _ ≫ (λ_ _).hom :=
  rfl

omit [Finite Λ] [HasTateTwist Λ] [HasCompactification a] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ Y] in
/-- In a monoidal category, `M ≅ M ⊗ 𝟙 ⟶ M ⊗ (T ⊗ N) ≅ (M ⊗ T) ⊗ N ⟶ N`, the last map being
`(M ⊗ T ⟶ M ⊗ 𝟙 ≅ M ⟶ 𝟙) ⊗ N` followed by the left unitor, is `M ⟶ 𝟙 ⟶ T ⊗ N ⟶ 𝟙 ⊗ N ≅ N`. -/
private lemma rightUnitor_inv_comp_whiskerLeft_comp_associator_inv_comp
    {C : Type*} [Category* C] [MonoidalCategory C] {M T N : C} (c : 𝟙_ C ⟶ T ⊗ N)
    (e : T ⟶ 𝟙_ C) (s : M ⟶ 𝟙_ C) :
    (ρ_ M).inv ≫ M ◁ c ≫ (α_ M T N).inv ≫ (M ◁ e ≫ (ρ_ M).hom ≫ s) ▷ N ≫ (λ_ N).hom =
      s ≫ c ≫ e ▷ N ≫ (λ_ N).hom := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc, triangle_assoc_comp_right_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc, leftUnitor_naturality, unitors_equal,
    Iso.inv_hom_id_assoc]
  simp only [Category.assoc]

/-- The untwisted smooth trace of `AlgebraicGeometry.Etale.TateOrientation.ofUnit` is the unit
trace followed by the isomorphism `Λ_Y ≅ Λ_Y(-d)` of `e`. -/
lemma untwistedSmoothTrace_ofUnit
    (o : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a)
    (e : tateObject Λ Y d ≅ 𝟙_ _) :
    (ofUnit o e).untwistedSmoothTrace = unitTrace o ≫ (unitIsoTateObjectNeg e).hom := by
  rw [untwistedSmoothTrace_eq, twistedSmoothTrace_ofUnit, unitIsoTateObjectNeg]
  exact rightUnitor_inv_comp_whiskerLeft_comp_associator_inv_comp _ _ _

end AlgebraicGeometry.Etale.TateOrientation
