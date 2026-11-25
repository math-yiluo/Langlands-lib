/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison

/-!
# The geometric comparison from the pro-etale to the etale site

The inclusion is the existing `Scheme.toProEt`, identity on schemes and arrows.
Its continuity and finite-limit preservation are the existing instances
`Scheme.isContinuous_toProEt` and `Scheme.preservesFiniteLimits_toProEt`.
The set adjunction below uses restriction and the left Kan extension followed by
sheafification, rather than a chosen abstract left adjoint. The coefficient version uses
these same constructions in modules over a fixed ring.

## References

* Stacks Project, Tag 099R, opening paragraph
* Sites, Tags 00WX, 00X6 and 00YV
* Stacks Project, Tags 099R, 00X6 and 00WJ
* Stacks Project, Tag 00YV, module paragraph
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The inverse image in `proEtaleSiteComparison` preserves finite limits, so this
adjunction is the geometric morphism from the pro-etale to the etale topos. -/
theorem preservesFiniteLimits_proEtaleSiteComparison (T : Scheme.{u}) :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (toProEt T)
        (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T)) := by
  have hlan : PreservesFiniteLimits
      ((toProEt T).op.lan : (T.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤
        (T.ProEtᵒᵖ ⥤ Type (u + 1))) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
      ((toProEt T).op.lan : (T.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤
        (T.ProEtᵒᵖ ⥤ Type (u + 1))) J
    intro K
    have : IsFiltered (CostructuredArrow (toProEt T).op K) :=
      IsFiltered.of_equivalence
        (structuredArrowOpEquivalence (toProEt T) (Opposite.unop K))
    exact preservesLimitsOfShape_of_natIso
      (Functor.lanEvaluationIsoColim' (toProEt T).op K).symm
  let _ := hlan
  apply Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
    (toProEt T) (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T)

/-- The same canonical comparison adjunction on sheaves of modules over a finite
(discrete) ring. The functors act on addition, zero, negation and scalar endomorphisms
by the module-valued Kan extension and sheafification. In particular this is the fixed
coefficient encoding of modules over the constant ring sheaf, not a structure-sheaf map. -/
noncomputable def proEtaleSiteComparisonModules (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⊣
      ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) T :=
  ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) T

end AlgebraicGeometry.Scheme
