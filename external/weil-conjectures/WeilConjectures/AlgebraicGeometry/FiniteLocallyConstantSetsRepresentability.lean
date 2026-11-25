/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale

/-! # Representability of finite locally constant sheaves of sets

Source: Stacks Project, Tag 03RV, implication (1) to (2).
(blueprint: lem-weil-pbc-finite-locally-constant-sets-representability)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Descent constructs a finite étale scheme representing a locally constant sheaf
of sets with finite geometric stalks. This is
`AlgebraicGeometry.Scheme.exists_iso_uliftYoneda_of_isFiniteLocallyConstant`.

Source: Stacks Project, Tag 03RV, implication (1) to (2).
(blueprint: lem-weil-pbc-finite-locally-constant-sets-representability) -/
theorem finiteLocallyConstant_sets_representable
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hloc : ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)))
    (hfin : IsFiniteSheaf E) :
    ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : Etale π),
      Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) :=
  exists_iso_uliftYoneda_of_isFiniteLocallyConstant E ⟨hloc, hfin⟩

end AlgebraicGeometry.Scheme
