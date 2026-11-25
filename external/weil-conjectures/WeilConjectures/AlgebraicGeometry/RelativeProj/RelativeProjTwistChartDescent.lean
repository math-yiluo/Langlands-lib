/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentCompatibility
import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentObject
import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentTransition

/-! # Descent of degree-one twists, before constructing a map from a base module

## References

* Stacks Project, Constructions, Tag 01NR
* Stacks, Tag 01NR, using the restriction and transitivity formulas in Tags 01N2 and 01MY
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- The affine twists descend with their restriction maps. This is object descent only:
there is no morphism from a module on the base in the conclusion. -/
theorem exists_twist_chart_descent :
    ∃ (L : A.relProj.Modules)
      (chart : ∀ U : S.affineOpens,
        (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
          Proj.twist (A.grading U) 1),
    ∀ (U V : S.affineOpens) (h : U ≤ V),
      ∃ t : Γ(Proj.twist (A.grading V) 1, A.twistChartOpen V) →+
          Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U),
        (∀ s : Γ(L, A.relProjHom ⁻¹ᵁ V.1),
          t (A.twistChartRead L chart V s) =
            A.twistChartRead L chart U
              (L.presheaf.map ((TopologicalSpace.Opens.map A.relProjHom.base).map
                (homOfLE (X := S.Opens) h)).op s)) ∧
        (∀ a : A.grading V 1,
          t (A.twistChartFraction V a) =
            A.twistChartFraction U ⟨A.res h a, (A.res h).map_mem a.property⟩) := by
  obtain ⟨L, chart, hcompat⟩ := A.exists_twist_chart_descent_object
  exact ⟨L, chart, A.exists_twist_chart_descent_transition L chart hcompat⟩

end AlgebraicGeometry.Scheme.GradedAlgebraData
