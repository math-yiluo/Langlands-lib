/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Filtered presentations by finite constructible complex hearts

Source: blueprint latest, sec-six-functors-basics/sk-prop-ind-heart,
sk-prop-ind-heart.proof.md, filtered-colimit heart construction, and the finite-complex
formulation of lem-sfb-finite-complex-heart-filtered-approximation
(blueprint: def-sfb-finite-constructible-complex-heart-presentations).

The complexes have arbitrary module differentials. Their zeroth cohomology modules
are the finite stages; arrows of the filtered presentation are arbitrary module maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

end AlgebraicGeometry.ProEtale
