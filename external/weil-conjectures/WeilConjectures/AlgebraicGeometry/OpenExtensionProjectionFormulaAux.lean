/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.OpenExtensionDerivedUnitIsIso
import WeilConjectures.AlgebraicGeometry.OpenExtensionTensorCounitIsIso

/-! Projection mate for transported open extension.
Source: Stacks Project, Tags 01AK, 06YB and 08BS.
(blueprint: lem-pc-open-extension-projection-formula). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable section
universe u w

local instance openExtensionProjectionStandardDerivedAux (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- The projection mate is invertible for the transported adjunction.
Source: Stacks Project, Tags 01AK, 06YB and 08BS.
(blueprint: lem-pc-open-extension-projection-aux).
Proof: the derived unit and the counit on J(A) tensor K are invertible. Tensoring
that unit with the identity and composing with the strong monoidal comparison gives
an invertible morphism f. The adjunction homEquiv_counit formula identifies its
transpose with J.map f followed by that counit, so both factors are invertible. -/
theorem openExtension_projection_formula_of_adjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∀ (m : R.Monoidal),
      letI := m
      ∀ (J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
        (adj : J ⊣ R),
        ∀ (A : schemeDerivedCategory U.toScheme) (K : schemeDerivedCategory X),
          IsIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
            ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
              (Functor.Monoidal.μIso R (J.obj A) K).hom)) := by
  dsimp
  intro m
  let _ := m
  intro J adj A K
  have : IsIso (adj.unit.app A) := openExtension_derived_unit_isIso X U J adj A
  have : IsIso (adj.counit.app (J.obj A ⊗ K)) :=
    openExtension_tensor_counit_isIso X U J adj A K
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙
      (Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)).mapDerivedCategory
  let f := (adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
    (Functor.Monoidal.μIso R (J.obj A) K).hom
  have hf : IsIso f := by dsimp [f]; infer_instance
  have h := adj.homEquiv_counit (A ⊗ R.obj K) (J.obj A ⊗ K) f
  exact h.symm ▸ (inferInstance : IsIso (J.map f ≫ adj.counit.app (J.obj A ⊗ K)))

end
end AlgebraicGeometry
