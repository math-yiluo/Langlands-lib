/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection

/-!
# Chart-compatible comparison of the two models of the projective line

Source: Stacks Project, Constructions, Tag 01NG; blueprint proof of
`theorem-riemann-roch-coherent-serre-duality` (blueprint: def-sc-p1-proj-chart-isomorphism).
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A comparison of polynomial Proj with the glued projective line, whose maps on the
standard charts send the coordinate to the ratio of the other variable to the chart variable.
Source: Stacks Project, Constructions, Tag 01NG.
(blueprint: def-sc-p1-proj-chart-isomorphism). -/
structure ProjChartIsomorphism (k : Type u) [Field k] where
  iso : Proj (homogeneousSubmodule (Fin 2) k) ≅ ProjectiveLine (Spec (.of k))
  chart_eq (i : ULift.{u} (Fin 2)) :
    Proj.awayι (homogeneousSubmodule (Fin 2) k) (X i.down)
        (isHomogeneous_X k i.down) Nat.one_pos ≫ iso.hom =
      Proj.linearChartHom (homogeneousSubmodule (Fin 2) k) (fun j : ULift.{u} (Fin 2) ↦ X j.down)
        (fun j ↦ X_mem_homogeneousSubmodule_one k j.down) i

end AlgebraicGeometry.ProjectiveLine
