/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Function fields of curves

Source: literature/blueprint/master/blueprint/sec-abelian-varieties/
def-sc-picard-group/def-sc-function-field.md,
node def-sc-function-field; Stacks Project, Morphisms, Lemma 01RV and
Definition 01RW (blueprint: def-sc-function-field).

The product definition below specializes to the node's curves over a field. Its finite
component indexing follows from finite type over a Noetherian field spectrum, as stated
in `lem-weil-pbc-finite-type-over-noetherian` and
`lem-weil-pbc-noetherian-finite-components`. The germ isomorphism with the rational-function
ring is stated separately by `lem-sc-rational-functions-generic-stalks`.

For the node's arbitrary integral scheme clause, use the existing `Scheme.functionField`,
the stalk at `genericPoint X`. Mathlib supplies its field instance and
`functionField_isFractionRing_of_isAffineOpen` for the germ algebra of every nonempty affine
open. The product below has just the whole space as its component in this case, so evaluation
at that component identifies it with the same generic stalk. These identifications are ring
isomorphisms, rather than definitional equalities between differently indexed carriers.
-/

@[expose] public section

universe u

open TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry

/-- The product of the structure-sheaf stalks at the generic points of all
irreducible components. For a curve this is its function field. The generic point is chosen
using scheme sobriety; components are closed, so `IsIrreducible.genericPoint` is a generic
point of the component itself, not merely of a larger closure. No reducedness is assumed:
the factors are local rings, and become fields in the integral case.
Source: blueprint node `def-sc-function-field`; Stacks Project, Morphisms, Lemma 01RV
and Definition 01RW (blueprint: def-sc-function-field). -/
noncomputable def Scheme.functionFieldOfComponents (X : Scheme.{u}) : CommRingCat.{u} :=
  CommRingCat.of
    (∀ Z : {s : Set X // s ∈ irreducibleComponents X},
      X.presheaf.stalk Z.property.1.genericPoint)

end AlgebraicGeometry
