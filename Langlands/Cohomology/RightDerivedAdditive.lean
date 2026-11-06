import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Additivity of right derived functors -/

open CategoryTheory

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

section Additive

variable {C : Type*} [Category C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category D] [Abelian D]

/-- Right derived functors of an additive functor are additive. -/
instance rightDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) : (F.rightDerived n).Additive where
  map_add {X Y f g} := by
    rw [F.rightDerived_map_eq n (f + g)
        (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X) +
          InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))
        (by rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
          InjectiveResolution.desc_commutes, Functor.map_add, Preadditive.add_comp]),
      F.rightDerived_map_eq n f _ (InjectiveResolution.desc_commutes _ _ _),
      F.rightDerived_map_eq n g _ (InjectiveResolution.desc_commutes _ _ _),
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

end Additive

end Langlands.AlgebraicGeometry.Modules.CechResolution
