/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.Abelian.PowShift
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterTower
public import WeilConjectures.CategoryTheory.Center.DerivedCategory

/-!
# Complete objects of the heart of a derived category

Let `C` be an abelian category with exact countable products and `z` an element of the center of
`C`, inducing the central element `z.derivedCategory` of `D(C)`. For an object `M` of `C`, if the
map `1 - powShift (z.app M) : ∏ₙ M ⟶ ∏ₙ M`, `(xₙ)ₙ ↦ (xₙ - z x_{n+1})ₙ` is an isomorphism, then
`M` placed in degree `0` is complete with respect to `z.derivedCategory`
(`CategoryTheory.Pretriangulated.isCenterComplete_singleFunctor_of_isIso`): the countable power
`∏ₙ M` in `D(C)` is computed in `C`, so the Milnor triangle of the tower `⋯ --z--> M --z--> M`
exhibits its homotopy limit as the fiber of the isomorphism `1 - powShift (z.app M)`, which
vanishes.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits _root_.Opposite

open scoped ZeroObject

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C]

omit [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions C]
  [HasExactLimitsOfShape (Discrete ℕ) C] in
/-- For an object `M` placed in degree `0` of a cochain complex, the degreewise central element
satisfies the completeness criterion `1 - powShift` invertible if `M` does. -/
lemma isIso_sub_powShift_single (z : CatCenter C) (M : C)
    (h : IsIso (𝟙 _ - powShift (z.app M))) :
    IsIso (𝟙 _ - powShift ((z.mapHomologicalComplex (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M))) := by
  have (i : ℤ) : IsIso ((𝟙 _ - powShift ((z.mapHomologicalComplex (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M))).f i) := by
    refine (isIso_map_sub_powShift_iff (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
      ((z.mapHomologicalComplex (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M))).2 ?_
    by_cases hi : i = 0
    · subst hi
      exact (isIso_sub_powShift_iff_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M) (z.naturality _).symm).2 h
    · exact isIso_sub_powShift_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **A module whose countable power is complete is complete in the derived category**: if
`1 - powShift (z.app M) : ∏ₙ M ⟶ ∏ₙ M` is an isomorphism, then `M` placed in degree `0` is
complete with respect to the central element `z.derivedCategory` of `D(C)`. -/
theorem isCenterComplete_singleFunctor_of_isIso (z : CatCenter C) (M : C)
    (h : IsIso (𝟙 _ - powShift (z.app M))) :
    IsCenterComplete z.derivedCategory ((DerivedCategory.singleFunctor C 0).obj M) := by
  let K := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let zc := z.mapHomologicalComplex (ComplexShape.up ℤ)
  have hK := isIso_sub_powShift_single z M h
  let F := centerTower z.derivedCategory (DerivedCategory.Q.obj K)
  let P : Fan fun n : ℕ ↦ F.obj (op n) :=
    Fan.mk (DerivedCategory.Q.obj (∏ᶜ fun _ : ℕ ↦ K))
      fun n ↦ DerivedCategory.Q.map (Pi.π (fun _ : ℕ ↦ K) n)
  let hP : IsLimit P := DerivedCategory.isLimitFanQ fun _ : ℕ ↦ K
  have ht : towerShift hP = DerivedCategory.Q.map (powShift (zc.app K)) :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [towerShift_proj]
      erw [centerTower_map_succ]
      rw [CatCenter.derivedCategory_app_Q_obj]
      simp only [P, fan_mk_proj, ← Functor.map_comp, powShift_π]
      rfl
  have hiso : IsIso (𝟙 P.pt - towerShift hP) := by
    have e : 𝟙 P.pt - towerShift hP = DerivedCategory.Q.map (𝟙 _ - powShift (zc.app K)) := by
      rw [ht, Functor.map_sub, Functor.map_id]
      rfl
    rw [e]
    exact Functor.map_isIso _ _
  let c : Cone F := { pt := 0, π := 0 }
  have hc : IsHomotopyLimit c := by
    refine ⟨P, hP, 0, isomorphic_distinguished _ (contractible_distinguished₁ P.pt) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (𝟙 P.pt - towerShift hP)).symm
        ((isZero_zero _).eq_of_src _ _) ?_ (by simp))⟩
    exact (IsIso.hom_inv_id (𝟙 P.pt - towerShift hP)).trans (id_comp (𝟙 P.pt)).symm
  exact (isCenterComplete_of_isHomotopyLimit_centerTower hc (isZero_zero _)).of_iso
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app M).symm

end CategoryTheory.Pretriangulated
