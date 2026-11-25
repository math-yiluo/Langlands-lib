/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentObject
import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentTransitionRead
import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentTransitionFraction

/-! # Transition part of relative Proj twist descent

## References

* Stacks Project, Constructions, Tag 01NR
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.GradedAlgebraData
variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- A compatible descended chart family has additive transitions compatible with readings
and fractions. -/
theorem exists_twist_chart_descent_transition
    (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
        Proj.twist (A.grading U) 1)
    (hcompat : TwistChartCompatibility A L chart) :
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
  classical
  intro U V h
  obtain ⟨θ, hθ, hsq⟩ := hcompat U V h
  let r := A.relProjFunctor.map (homOfLE h)
  have hr : r ≫ A.relProjι V = A.relProjι U := by
    exact A.relProjFunctor_map_relProjι (homOfLE h)
  have hopen : r ⁻¹ᵁ A.twistChartOpen V = A.twistChartOpen U := by
    simp only [twistChartOpen, A.relProjHom_preimage,
      Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]
  let t : Γ(Proj.twist (A.grading V) 1, A.twistChartOpen V) →+
      Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U) :=
    ConcreteCategory.hom
      (((Scheme.Modules.tensorPullbackSectionAdjunction r).unit.app
          (Proj.twist (A.grading V) 1)).app (A.twistChartOpen V) ≫
        (θ 1).hom.app (r ⁻¹ᵁ A.twistChartOpen V) ≫
        eqToHom (congrArg (fun W => Γ(Proj.twist (A.grading U) 1, W)) hopen))
  refine ⟨t, ?_, ?_⟩
  · intro s
    simpa [t] using
      (A.twist_chart_transition_read L chart U V h θ hθ hsq hopen s)
  · intro a
    simpa [t] using
      (A.twist_chart_transition_fraction L chart U V h θ hθ hsq hopen a)

end AlgebraicGeometry.Scheme.GradedAlgebraData
