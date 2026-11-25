/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Componentwise normalization

## References

* Stacks Project, Morphisms, Tag 0CDV
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The reduced induced scheme on an irreducible component, defined by its vanishing ideal. -/
noncomputable def reducedNormalizationComponent (X : Scheme.{u})
    (Z : irreducibleComponents X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal
    ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subscheme

/-- The reduced induced structure on an irreducible component is integral. -/
theorem isIntegral_reducedNormalizationComponent (X : Scheme.{u})
    (Z : irreducibleComponents X) : IsIntegral (X.reducedNormalizationComponent Z) := by
  let : IrreducibleSpace (X.reducedNormalizationComponent Z) := by
    change IrreducibleSpace (Z.1 : Set X)
    exact Subtype.irreducibleSpace Z.2.1
  let : IsReduced (X.reducedNormalizationComponent Z) := by
    unfold reducedNormalizationComponent
    infer_instance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

attribute [instance] isIntegral_reducedNormalizationComponent

/-- The disjoint union of the function-field normalizations of the reduced components. -/
noncomputable def reducedNormalization (X : Scheme.{u}) : Scheme.{u} :=
  ∐ (fun Z : irreducibleComponents X ↦ (X.reducedNormalizationComponent Z).normalization)

/-- The canonical map from the componentwise normalization. -/
noncomputable def fromReducedNormalization (X : Scheme.{u}) : X.reducedNormalization ⟶ X :=
  Sigma.desc (fun Z : irreducibleComponents X ↦
    (X.reducedNormalizationComponent Z).fromNormalization ≫
      (IdealSheafData.vanishingIdeal
        ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι)

end AlgebraicGeometry.Scheme
