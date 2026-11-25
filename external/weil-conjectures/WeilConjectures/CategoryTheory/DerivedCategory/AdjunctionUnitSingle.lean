/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit

/-!

# The derived unit on a single object, after an exact functor

Let `f ⊣ g` be an adjunction between abelian categories with `f` exact, and let `h` be an exact
functor out of the source of `f`. For an object `M`, the unit of the derived adjunction
`f.leftDerivedFunctor ⊣ g.rightDerivedFunctor` at `M[0]` is a morphism
`M[0] ⟶ Rg (Lf (M[0])) ≅ Rg ((f M)[0])`. Its cohomology in degree `0` is the unit
`M ⟶ g (f M)` of `f ⊣ g`, and its cohomology in degree `n > 0` has target `Rⁿg (f M)`.
Hence it becomes an isomorphism after applying `h` levelwise as soon as `h` inverts the unit
`M ⟶ g (f M)` and kills the higher derived functors `Rⁿg (f M)`
(`CategoryTheory.Adjunction.isIso_mapDerivedCategory_map_derivedAdjunction_unit_app`).

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions D] [EnoughInjectives D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  (adj : f ⊣ g) (h : C ⥤ E) [h.Additive] [PreservesFiniteLimits h] [PreservesFiniteColimits h]

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C] in
/-- Let `g` be left exact and `h` exact. If `h` kills `Rⁿg N` for `n > 0`, then `h` applied
levelwise inverts the right-derived unit `(g N)[0] ⟶ Rg (N[0])`: in degree `0` this unit is an
isomorphism on cohomology, in degrees `n > 0` its target has cohomology `Rⁿg N`, and in degrees
`n < 0` both sides vanish. -/
theorem _root_.CategoryTheory.Functor.isIso_mapDerivedCategory_map_rightDerivedSingleUnit
    (g : D ⥤ C) [g.Additive] [PreservesFiniteLimits g] (N : D)
    (hpos : ∀ n : ℕ, 0 < n → IsZero (h.obj ((g.rightDerived n).obj N))) :
    IsIso (h.mapDerivedCategory.map (g.rightDerivedSingleUnit N)) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine (NatIso.isIso_map_iff (h.mapDerivedCategoryHomologyFunctorIso n) _).1 ?_
  dsimp only [Functor.comp_map]
  have hzero {X Y : C} (u : X ⟶ Y) (hX : IsZero X) (hY : IsZero (h.obj Y)) : IsIso (h.map u) :=
    ⟨⟨0, (h.map_isZero hX).eq_of_src _ _, hY.eq_of_src _ _⟩⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := g.isGE_rightDerivedFunctor_obj_singleFunctor N
    exact hzero _ (((DerivedCategory.singleFunctor C 0).obj (g.obj N)).isZero_of_isGE 0 n hn)
      (h.map_isZero ((g.rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor D 0).obj N)).isZero_of_isGE 0 n hn))
  · have e := g.rightDerivedSingleUnit_zero N
    rw [← Iso.eq_comp_inv] at e
    rw [e]
    infer_instance
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
    exact hzero _ (((DerivedCategory.singleFunctor C 0).obj (g.obj N)).isZero_of_isLE 0 m hn)
      ((hpos m (by exact_mod_cast hn)).of_iso
        (h.mapIso (g.homologyRightDerivedFunctorObjSingleFunctorIso N m)))

/-- Let `f ⊣ g` with `f` exact and let `h` be exact. If `h` inverts the unit `M ⟶ g (f M)` and
kills `Rⁿg (f M)` for `n > 0`, then `h` applied levelwise inverts the unit
`M[0] ⟶ Rg (Lf (M[0]))` of the derived adjunction. -/
theorem isIso_mapDerivedCategory_map_derivedAdjunction_unit_app (M : C)
    (h₀ : IsIso (h.map (adj.unit.app M)))
    (hpos : ∀ n : ℕ, 0 < n → IsZero (h.obj ((g.rightDerived n).obj (f.obj M)))) :
    IsIso (h.mapDerivedCategory.map
      (adj.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj M))) := by
  have : PreservesFiniteLimits g := by
    have := adj.rightAdjoint_preservesLimits
    infer_instance
  let K := (HomotopyCategory.quotient C (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)
  let e := (f.mapCochainComplexSingleFunctor 0).app M
  let u := (adj.mapHomologicalComplex (.up ℤ)).unit.app ((CochainComplex.singleFunctor C 0).obj M)
  have h₁ := adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit K
  have h₂ := g.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient D (.up ℤ)).map e.hom)
  have h₃ : g.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj ((CochainComplex.singleFunctor D 0).obj
        (f.obj M))) =
      DerivedCategory.Q.map ((g.mapCochainComplexSingleFunctor 0).hom.app (f.obj M)) ≫
        g.rightDerivedSingleUnit (f.obj M) := by
    rw [Functor.rightDerivedSingleUnit]
    erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
    rfl
  have h₄ := Adjunction.mapHomotopyCategory_unit_app_quotient (c := .up ℤ) adj
    ((CochainComplex.singleFunctor C 0).obj M)
  have key : adj.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
      g.rightDerivedFunctor.map (f.leftDerivedFunctorCounit.app K) ≫
        g.rightDerivedFunctor.map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map e.hom)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map u) ≫
        DerivedCategory.Qh.map ((g.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient D (.up ℤ)).map e.hom)) ≫
        DerivedCategory.Q.map ((g.mapCochainComplexSingleFunctor 0).hom.app (f.obj M)) ≫
        g.rightDerivedSingleUnit (f.obj M) := by
    erw [reassoc_of% h₁]
    rw [h₄]
    erw [← h₂, h₃]
    rfl
  have hu : IsIso ((h.mapHomologicalComplex (.up ℤ)).map u) := by
    have hY (Y : C) (eY : Y ≅ M) : IsIso (h.map (adj.unit.app Y)) := by
      have hY : adj.unit.app Y = eY.hom ≫ adj.unit.app M ≫ g.map (f.map eY.inv) := by simp
      rw [hY, h.map_comp, h.map_comp]
      infer_instance
    have (i : ℤ) : IsIso (((h.mapHomologicalComplex (.up ℤ)).map u).f i) := by
      by_cases hi : i = 0
      · subst hi
        exact hY _ (HomologicalComplex.singleObjXSelf _ 0 M)
      · have hX := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
        exact ⟨⟨0, (h.map_isZero hX).eq_of_src _ _,
          (h.map_isZero (g.map_isZero (f.map_isZero hX))).eq_of_src _ _⟩⟩
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQu : IsIso (h.mapDerivedCategory.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map u))) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      h.mapDerivedCategory ≪≫ h.mapDerivedCategoryFactors) u).2
        (inferInstanceAs (IsIso (DerivedCategory.Q.map _)))
  have hR := Functor.isIso_mapDerivedCategory_map_rightDerivedSingleUnit h g (f.obj M) hpos
  have hk : IsIso (h.mapDerivedCategory.map
      (adj.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        g.rightDerivedFunctor.map (f.leftDerivedFunctorCounit.app K) ≫
        g.rightDerivedFunctor.map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map e.hom)))) := by
    rw [key]
    erw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    exact IsIso.comp_isIso' hQu (IsIso.comp_isIso'
      (Iso.isIso_hom (h.mapDerivedCategory.mapIso (DerivedCategory.Qh.mapIso
        ((g.mapHomotopyCategory (.up ℤ)).mapIso
          ((HomotopyCategory.quotient D (.up ℤ)).mapIso e)))))
      (IsIso.comp_isIso' (Iso.isIso_hom (h.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso
        ((g.mapCochainComplexSingleFunctor 0).app (f.obj M))))) hR))
  have hc : IsIso (h.mapDerivedCategory.map
      (g.rightDerivedFunctor.map (f.leftDerivedFunctorCounit.app K) ≫
        g.rightDerivedFunctor.map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map e.hom)))) := by
    erw [Functor.map_comp]
    exact IsIso.comp_isIso' inferInstance (Iso.isIso_hom (h.mapDerivedCategory.mapIso
      (g.rightDerivedFunctor.mapIso (DerivedCategory.Qh.mapIso
        ((HomotopyCategory.quotient D (.up ℤ)).mapIso e)))))
  erw [Functor.map_comp] at hk
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hc hk

end CategoryTheory.Adjunction
