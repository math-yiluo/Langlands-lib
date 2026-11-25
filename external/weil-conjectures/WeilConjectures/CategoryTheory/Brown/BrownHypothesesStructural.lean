/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import Mathlib.CategoryTheory.Idempotents.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete

/-!
# Ambient structures of the constructible localizing closure

The ambient structures in Brown's hypotheses hold for arbitrary condensed coefficients.
Source: blueprint lemma-hypotheses-brown-representability, proof paragraph 1.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- Structural part of the Brown-hypotheses conclusion.
Source: blueprint main-20261015, lemma-hypotheses-brown-representability, proof paragraph 1.
The proof packages the generic localizing-closure ambient structures.
No field or coefficient admissibility hypothesis is needed.
(blueprint: h1-brown-hypotheses-structural). -/
theorem brownHypotheses_structural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    LocallySmall.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory ∧
      ∃ hTri : (localizingClosureProEtale Λ X).IsTriangulated,
        let := hTri
        (localizingClosureProEtale Λ X).IsClosedUnderIsomorphisms ∧
          IsIdempotentComplete (localizingClosureProEtale Λ X).FullSubcategory ∧
          ∃ _ : HasCoproducts.{u + 1}
              (localizingClosureProEtale Λ X).FullSubcategory, True := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : HasDerivedCategory.{u + 1} A := inferInstance
  let S := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  obtain ⟨hcop, _, _, hloc, _, _, _, _⟩ := localizingClosure_exists Λ X S
  have hLocSmall : LocallySmall.{u + 1} L.FullSubcategory :=
    locallySmall_of_faithful L.ι
  have htri : L.IsTriangulated := hloc.1
  let := htri
  have hiso : L.IsClosedUnderIsomorphisms := hloc.2.1
  have hclosed (I : Type (u + 2)) : L.IsClosedUnderColimitsOfShape (Discrete I) :=
    hloc.isClosedUnderColimitsOfShape_discrete I
  have hsum : HasCoproducts.{u + 1} L.FullSubcategory := by
    intro I
    have := hclosed (ULift.{u + 2} I)
    let : L.IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence Equiv.ulift)
    exact hasColimitsOfShape_of_closedUnderColimits (Discrete I) L
  let := hsum
  have hid : IsIdempotentComplete L.FullSubcategory :=
    isIdempotentComplete_of_countableCoproducts L.FullSubcategory
  exact ⟨hLocSmall, ⟨htri, hiso, hid, ⟨hsum, trivial⟩⟩⟩

end CategoryTheory
