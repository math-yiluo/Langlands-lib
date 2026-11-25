/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Invertibility of the bounded below derived unit

Let `adj : L ⊣ R` be an adjunction of additive functors between abelian categories with
enough injectives, with `L` exact and `R` left exact. Suppose that the unit of `adj` is an
isomorphism on injective objects and that `L` sends injective objects to `R`-acyclic objects.
Then the unit of the bounded below derived adjunction
`adj.derivedPlus : L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus` is an isomorphism.

Indeed, every object of the bounded below derived category is represented by a bounded below
complex `I` of injectives; on it the derived unit is the unit of `adj` on `I`, an isomorphism
termwise, followed by the unit `R(L(I)) ⟶ R⁺R(L(I))` of the right derived functor, which is an
isomorphism since `L(I)` is a bounded below complex of `R`-acyclic objects
(`Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`).

## Main results

- `CategoryTheory.Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic`: the derived unit is
  invertible under the above hypotheses.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R] (adj : L ⊣ R)

/-- If the unit of `adj : L ⊣ R` is an isomorphism on injective objects and `L` sends injective
objects to `R`-acyclic objects, then the unit of the bounded below derived adjunction
`L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus` is an isomorphism.

On a bounded below complex `I` of injectives the derived unit factors as

```
  I --adj.unit--> R (L I) --unit of R⁺--> R⁺R (L I)
```

where the first map is invertible termwise by `h₁` and the second because `L I` is a complex of
`R`-acyclic objects by `h₂`. -/
theorem isIso_derivedPlus_unit_app_of_rightAcyclic
    (h₁ : ∀ (I : C) [Injective I], IsIso (adj.unit.app I))
    (h₂ : ∀ (I : C) [Injective I], R.rightAcyclic (L.obj I)) (X : DerivedCategory.Plus C) :
    IsIso (adj.derivedPlus.unit.app X) := by
  -- represent `X` by a bounded below complex of injectives `T`
  obtain ⟨K, ⟨e⟩⟩ : ∃ K : HomotopyCategory.Plus C,
      Nonempty (DerivedCategory.Plus.Qh.obj K ≅ X) :=
    ⟨_, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso X⟩⟩
  obtain ⟨M, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  obtain ⟨a, _⟩ := M.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective M a
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
  rw [← NatTrans.isIso_app_iff_of_iso _ e,
    NatTrans.isIso_app_iff_of_iso _
      (asIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)))]
  -- on `T`, the derived unit is the unit of `adj` followed by the unit of `R⁺R`
  set K' := (HomotopyCategory.Plus.quotient C).obj T'
  have hu : IsIso (adj.mapHomotopyCategoryPlus.unit.app K') := by
    have : IsIso ((HomotopyCategory.Plus.ι C).map (adj.mapHomotopyCategoryPlus.unit.app K')) := by
      rw [ι_map_mapHomotopyCategoryPlus_unit_app]
      change IsIso ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient C _).obj T'.obj))
      rw [mapHomotopyCategory_unit_app_quotient]
      have (n : ℤ) : IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
          T'.obj).f n) := by
        rw [mapHomologicalComplex_unit_app_f]
        exact h₁ _
      have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app T'.obj) :=
        HomologicalComplex.Hom.isIso_of_components _
      exact Functor.map_isIso _ _
    exact isIso_of_fully_faithful (HomotopyCategory.Plus.ι C) _
  let LT : CochainComplex.Plus D := ⟨(L.mapHomotopyCategoryPlus.obj K').obj.as,
    (HomotopyCategory.plus_quotient_obj_iff _).1 (L.mapHomotopyCategoryPlus.obj K').property⟩
  have hR : IsIso (R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj K')) :=
    R.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic LT (fun n ↦ h₂ (T'.obj.X n))
  have hfac := adj.derivedPlus_unit_app_fac K'
  have : IsIso (adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj K') ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K')) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (R.rightDerivedFunctorPlus.map
    (L.mapDerivedCategoryPlusFactorsh.hom.app K'))

end CategoryTheory.Adjunction
