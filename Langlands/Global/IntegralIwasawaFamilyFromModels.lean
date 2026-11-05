import Langlands.Global.IntegralIwasawaFamilyStatement
import Langlands.Global.CanonicalIntegralModelCompletions

/-! # Assembling an integral Iwasawa family from actual local model properties -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Pointwise ValuativeRel

namespace Langlands.Global.IntegralIwasawaFamily

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
  (S : Finset (FinitePlace F))
  (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)

local instance modelFamilyPointsTopology (v : FinitePlace F) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
  G.affinePointsTopologicalSpace _

/-- The two remaining local properties of a supplied arithmetic model. -/
structure ModelLocalConditions : Prop where
  maximal : ∀ (v : {v : FinitePlace F // v ∉ S})
    (L : Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1)))),
    IsCompact (L : Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1)))) →
      IntegralModelCompletions.subgroup F S v M ≤ L →
        L = IntegralModelCompletions.subgroup F S v M
  covering : ∀ v : {v : FinitePlace F // v ∉ S},
    Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v.1))) *
      (IntegralModelCompletions.subgroup F S v M : Set _) = Set.univ

/-- The fixed finite-type family satisfies all three required conditions once
the supplied model has the two local structural properties. -/
theorem isIntegralIwasawaFamily_of_models
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (h : ModelLocalConditions F G P p S M) :
    IsIntegralIwasawaFamily F G P p (FiniteTypeIntegralFamily.subgroup F G) := by
  refine ⟨?_, FiniteTypeIntegralFamily.eventually_projection_mem F G,
    FiniteTypeIntegralFamily.eventually_uniform_integral F G⟩
  filter_upwards [IntegralModelCompletions.eventually_subgroup_eq F S M,
    S.eventually_cofinite_notMem] with v heq hv
  refine ⟨FiniteTypeIntegralFamily.isCompact_subgroup F G v, ?_, ?_⟩
  · rw [heq hv]
    exact h.maximal ⟨v, hv⟩
  · rw [heq hv]
    exact h.covering ⟨v, hv⟩

namespace ModelLocalConditions

local instance familyCompletionValuativeRel (v : FinitePlace F) :
    ValuativeRel (FiniteCompletion F v) :=
  FiniteCompletion.valuativeRel v

private instance familyCompletionAffine [IsAffine G.X.left] (v : FinitePlace F) :
    IsAffine
      ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).obj G).X.left := by
  change IsAffine (Limits.pullback G.X.hom (Spec.algebraMap F (FiniteCompletion F v)))
  infer_instance

local instance familyCompletionRationalTopology [IsAffine G.X.left] (v : FinitePlace F) :
    TopologicalSpace
      (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).obj G)) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology (FiniteCompletion F v) _

/-- Local maximality and parabolic-left covering on the canonical integer models
give the same properties on the original completion coefficient-point carrier. -/
theorem of_canonicalModels [IsAffine G.X.left]
    (hmax : ∀ (v : {v : FinitePlace F // v ∉ S})
      (L : Subgroup (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G))),
      IsCompact (L : Set (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G))) →
        (IntegralModelCompletions.canonicalModel F S v M).integralPoints ≤ L →
          L = (IntegralModelCompletions.canonicalModel F S v M).integralPoints)
    (hcover : ∀ v : {v : FinitePlace F // v ∉ S},
      Set.range (rationalPoints.map
          ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).map p)) *
        ((IntegralModelCompletions.canonicalModel F S v M).integralPoints : Set _) =
          Set.univ) :
    ModelLocalConditions F G P p S M where
  maximal v := IntegralModelCompletions.subgroup_maximal_of_canonicalModel F S v M (hmax v)
  covering v := IntegralModelCompletions.subgroup_covering_of_canonicalModel
    F S v M p (hcover v)

end ModelLocalConditions

end Langlands.Global.IntegralIwasawaFamily
