/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientPreviousLocalComplexesChartHomology

/-! # Constant realization and scalar restriction

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EL.
(blueprint: lem-weil-pbc-constant-realization-restriction-underlying).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The constant scalar-restriction comparison has identity underlying abelian sheaf map.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EL.
(blueprint: lem-weil-pbc-constant-realization-restriction-underlying).

Proof: take the module-sheafification comparison induced by the unit. Forgetting
scalars identifies its defining presheaf map with the abelian sheafification unit.
The adjunction bijection sends that unit to the identity. -/
theorem constantRealization_restrictionIso_exists (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D] (f : B →+* D) (M : ModuleCat.{t} D) :
    ∃ e : (ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
          (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
            koszulConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M) ≅
        (SheafOfModules.restrictScalars (adicModuleMap X f)).obj
          ((ModuleCat.uliftFunctor.{t + 1, t} D ⋙ ModuleCat.restrictScalars.{t + 1}
            (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom ⋙
              koszulConstantFunctor X D).obj M),
      (SheafOfModules.toSheaf (adicModuleRing X B)).map e.hom = 𝟙 _ := by
  refine ⟨constantRestrictionIso X f M, ?_⟩
  unfold constantRestrictionIso
  dsimp only [asIso]
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  change ((sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{t + 1}).homEquiv
    _ _).symm (toSheafify (ProEt.topology X) _) = 𝟙 _
  apply ((sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{t + 1}).homEquiv
    _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (Category.comp_id _).symm

end AlgebraicGeometry.Scheme
