/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! # The published scalar comparisons satisfy their normalizations

Keep the normalization choose-spec calculations at generic coefficient rings.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale.ExceptionalCoefficients

/-- The actual published unit and tensor comparisons satisfy their all-complex
representative equations.
Source: Stacks 07A4; the unique normalizations defining these comparisons
(blueprint: lem-coef-etale-scalar-normalizations).

Proof: unitIso is chosen from unitIso_existsUnique, whose choose_spec gives its
normalization. The site tensorIso is heterogeneously equal to the comparison chosen
from tensorIso_existsUnique. Convert that equality to equality and transport the
latter comparison's choose_spec normalization along it. -/
theorem scalarExtension_normalizations
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    UnitNormalization φ T (unitIso φ T) ∧ TensorNormalization φ T (tensorIso φ T) := by
  refine ⟨(unitIso_existsUnique φ T).choose_spec.1, ?_⟩
  have htensor : tensorIso φ T = (tensorIso_existsUnique φ T).choose :=
    eq_of_heq (siteTensorIso_existsUnique φ T).choose_spec.1
  exact htensor.symm ▸ (tensorIso_existsUnique φ T).choose_spec.1

end AlgebraicGeometry.Etale.ExceptionalCoefficients
