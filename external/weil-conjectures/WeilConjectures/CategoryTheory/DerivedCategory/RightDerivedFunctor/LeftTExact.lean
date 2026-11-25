/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# The total right derived functor is left t-exact

`CategoryTheory.Functor.isGE_rightDerivedFunctor_obj`: if a complex `K` has no homology in
degrees `< n`, neither has `RF(K)`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]

/-- **The total right derived functor is left t-exact**: if `K` has no homology in degrees
`< n`, neither has `RF(K)`. Indeed `K` lies in the bounded below derived category, on which
`RF` is computed by `R⁺F`. -/
lemma isGE_rightDerivedFunctor_obj (K : DerivedCategory C) (n : ℤ) [K.IsGE n] :
    (F.rightDerivedFunctor.obj K).IsGE n := by
  let K' : DerivedCategory.Plus C := ⟨K, ⟨n, inferInstance⟩⟩
  have : K'.IsGE n := (K'.isGE_ι_obj_iff n).1 ‹_›
  refine (DerivedCategory.isGE_iff _ n).2 fun q hq ↦ ?_
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K' n hq).of_iso
    ((DerivedCategory.homologyFunctor D q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app K')).symm

end CategoryTheory.Functor
