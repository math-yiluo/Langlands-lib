/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionOrdinaryComparisonExistence
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionDerivedComparisonExistence

/-! Comparison and normalization for a fixed sectionwise scalar model.

## References

* Stacks 03EK, 06YY, 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- For any fixed actual cochain model, normalized ordinary and derived section
comparisons exist. -/
theorem scalar_section_comparisons_exists (T : Scheme.{u})
    (model : SectionModel a T) :
    ∃ ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ≅
      (equivalence Λ T).functor ⋙ model.E,
      ∃ derived : D a T ⋙ derivedFunctor Λ' T ≅
        derivedFunctor Λ T ⋙ model.T,
        ScalarSectionNormalized a T
          { model := model, ordinary := ordinary, derived := derived } := by
  obtain ⟨ordinary, hordinary⟩ := scalar_section_ordinary_comparison_exists a T model
  obtain ⟨derived, hderived⟩ :=
    scalar_section_derived_comparison_exists a T model ordinary
  exact ⟨ordinary, derived, hordinary, hderived⟩

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
