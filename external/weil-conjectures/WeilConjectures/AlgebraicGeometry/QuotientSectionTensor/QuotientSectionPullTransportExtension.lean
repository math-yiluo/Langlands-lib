/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportKFlat
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportLocalization

/-! # Localization extension for normalized quotient section pull transport

## References

* Stacks 06YS and 06YU
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- Flat-term computation equations extend to every complex in the derived
category. The extension is the resolving-class/localization step and is strictly
weaker than constructing the comparison itself.
-/
theorem section_pull_transport_extend_kflat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T)
    (hflat : SectionPullNormalizedOnKFlat a f cX cY barLam) :
    SectionPullNormalized a f cX cY barLam := by
  rcases hflat with ⟨e, hordinary, hcomputation⟩
  refine ⟨e, hordinary, ?_⟩
  exact section_pull_normalized_localization_descent
    a f cX cY barLam e hcomputation

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
