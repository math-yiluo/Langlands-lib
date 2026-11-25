/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistComparison
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist

/-! # Compatibility data for relative Proj twist charts

## References

* Stacks Project, Constructions, Tag 01NR
* Stacks Project, Constructions, Tags 01N2, 01MY and 01NR
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- The open on which a chart reads the sections above its base open. -/
noncomputable def twistChartOpen (U : S.affineOpens) : (Proj (A.grading U)).Opens :=
  A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ U.1)

/-- A homogeneous element, viewed as a section of the affine degree-one twist. -/
noncomputable def twistChartFraction (U : S.affineOpens) (a : A.grading U 1) :
    Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U) :=
  (Proj.unitToTwist a.property).app (A.twistChartOpen U)
    (1 : Γ(Proj (A.grading U), A.twistChartOpen U))

/-- Reading a global module section in an affine twist chart, using the actual tensor unit. -/
noncomputable def twistChartRead (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅ Proj.twist (A.grading U) 1)
    (U : S.affineOpens) :
    ((Scheme.Modules.pushforward A.relProjHom).obj L).val.obj (op U.1) ⟶
      ((Scheme.Modules.pushforward A.relProjHom).obj
        ((Scheme.Modules.pushforward (A.relProjι U)).obj
          (Proj.twist (A.grading U) 1))).val.obj (op U.1) :=
  (((Scheme.Modules.pushforward A.relProjHom).map
    ((Scheme.Modules.tensorPullbackSectionAdjunction (A.relProjι U)).unit.app L ≫
      (Scheme.Modules.pushforward (A.relProjι U)).map (chart U).hom)).val.app (op U.1))

/-- Compatibility of chart choices with normalized scalar-extension comparisons.

For every affine restriction, the comparison is required to be the normalized one from
`scalarExtension_twist_comparison`, and the chart square is required to commute after the
canonical tensor-pullback composition isomorphism. -/
def TwistChartCompatibility (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
        Proj.twist (A.grading U) 1) : Prop :=
  ∀ (U V : S.affineOpens) (h : U ≤ V),
    ∃ θ : ∀ j : ℤ,
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
          (Proj.twist (A.grading V) j) ≅ Proj.twist (A.grading U) j,
      Proj.IsScalarExtensionTwistComparison (A.res h)
          (A.relProjFunctor.map (homOfLE h)) θ ∧
        (eqToIso (congrArg (fun f ↦
            (Scheme.Modules.tensorPullback f).obj L)
          (A.relProjFunctor_map_relProjι (homOfLE h)).symm) ≪≫
          (Scheme.Modules.tensorPullbackSectionComp
            (A.relProjFunctor.map (homOfLE h)) (A.relProjι V)).app L ≪≫
          (Scheme.Modules.tensorPullback
            (A.relProjFunctor.map (homOfLE h))).mapIso (chart V) ≪≫ θ 1 = chart U)

end AlgebraicGeometry.Scheme.GradedAlgebraData
