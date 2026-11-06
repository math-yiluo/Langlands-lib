import Langlands.GroupScheme.RelativeParabolicQuotientStatement
import Langlands.GroupScheme.IntegralParabolicCovering
import Langlands.Global.GoodIntegralModelCompletions
import Langlands.Global.IntegralIwasawaFamilyFromModels

/-! # Parabolic-left coverings of good model data from relative parabolic quotients -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise ValuativeRel

namespace Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading.ModelData

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {G P : GroupScheme (Spec (CommRingCat.of K))} {p : P ⟶ G}
  (hQ : RelativeParabolicQuotient.ExistenceStatement.{u}) (D : ModelData R K p)

include hQ

/-- The relative parabolic quotient statement applies to the integral models of model data. -/
theorem exists_quotient :
    ∃ (Q : Over (Spec (CommRingCat.of R))) (q : D.ambient.group.X ⟶ Q),
      IsProper Q.hom ∧ Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ D.ambient.group.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range D.inclusion.hom).carrier T :=
  hQ R D.ambient.group D.parabolic.group D.inclusion.hom D.reductive D.parabolicSmooth
    D.closedImmersion fun k _ _ => D.fieldParabolic k

/-- A chosen quotient scheme of the ambient model by the subgroup model. -/
def quotient : Over (Spec (CommRingCat.of R)) :=
  (exists_quotient hQ D).choose

/-- The chosen quotient morphism of the ambient model. -/
def quotientMap : D.ambient.group.X ⟶ quotient hQ D :=
  (exists_quotient hQ D).choose_spec.choose

/-- The chosen quotient is proper, its morphism is flat, surjective and quasi-compact,
and its fibres are exactly the right cosets of the subgroup model. -/
theorem quotientMap_spec :
    IsProper (quotient hQ D).hom ∧ Flat (quotientMap hQ D).left ∧
      Surjective (quotientMap hQ D).left ∧ QuasiCompact (quotientMap hQ D).left ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ D.ambient.group.X),
        g ≫ quotientMap hQ D = h ≫ quotientMap hQ D ↔
          g⁻¹ * h ∈ (SubgroupFunctor.range D.inclusion.hom).carrier T :=
  (exists_quotient hQ D).choose_spec.choose_spec

omit hQ in
/-- The subgroup model has a connected special fibre. -/
theorem hasConnectedSpecialFibre [IsLocalRing R] : D.parabolic.HasConnectedSpecialFibre :=
  (D.goodFieldFibers.atFieldPoint (IsLocalRing.ResidueField R)
    (IntegralModel.residueBaseMap R)).2.2

/-- Over a complete valuation ring with finite residue field, model data have the
parabolic-left integral covering of the generic group. -/
theorem range_mul_integralPoints_eq_univ [ValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    Set.range (rationalPoints.map p) *
      (D.ambient.integralPoints : Set (rationalPoints G)) = Set.univ := by
  obtain ⟨hproper, hflat, hsurj, hqc, hfib⟩ := quotientMap_spec hQ D
  have : IsClosedImmersion D.inclusion.hom.hom.hom.left := D.closedImmersion
  have : Mono D.inclusion.hom.hom.hom := Over.mono_of_mono_left _
  exact IntegralParabolicCovering.range_mul_integralPoints_eq_univ D.ambient D.parabolic
    D.inclusion (quotientMap hQ D) D.parabolicSmooth D.hasConnectedSpecialFibre hfib

end Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading.ModelData

namespace Langlands.Global.IntegralIwasawaFamily

open Langlands.GroupScheme
open Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

variable (F : Type u) [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  (S : Finset (FinitePlace F))

local instance quotientCoveringValuativeRel (v : FinitePlace F) :
    ValuativeRel (FiniteCompletion F v) :=
  FiniteCompletion.valuativeRel v

private instance quotientCoveringAffine [IsAffine G.X.left] (v : FinitePlace F) :
    IsAffine
      ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).obj G).X.left := by
  change IsAffine (Limits.pullback G.X.hom (Spec.algebraMap F (FiniteCompletion F v)))
  infer_instance

local instance quotientCoveringRationalTopology [IsAffine G.X.left] (v : FinitePlace F) :
    TopologicalSpace
      (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).obj G)) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology (FiniteCompletion F v) _

/-- The canonical-integer specialization of good S-integer model data has the
parabolic-left covering at every place outside `S`. -/
theorem canonicalModel_covering (hQ : RelativeParabolicQuotient.ExistenceStatement.{u})
    (D : ModelData ((S : Set (FinitePlace F)).integer F) F p)
    (v : {v : FinitePlace F // v ∉ S}) :
    Set.range (rationalPoints.map
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).map p)) *
      ((IntegralModelCompletions.canonicalModel F S v D.ambient).integralPoints : Set _) =
        Set.univ := by
  have : IsNonarchimedeanLocalField (FiniteCompletion F v.1) :=
    FiniteCompletion.isNonarchimedeanLocalField v.1
  exact (IntegralModelCompletions.canonicalModelData F S v D).range_mul_integralPoints_eq_univ hQ

/-- With the relative quotient statement, the local covering condition holds, so only
local maximality on the canonical models remains for `ModelLocalConditions`. -/
theorem ModelLocalConditions.of_quotientStatement [IsAffine G.X.left]
    (hQ : RelativeParabolicQuotient.ExistenceStatement.{u})
    (D : ModelData ((S : Set (FinitePlace F)).integer F) F p)
    (hmax : ∀ (v : {v : FinitePlace F // v ∉ S})
      (L : Subgroup (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G))),
      IsCompact (L : Set (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G))) →
        (IntegralModelCompletions.canonicalModel F S v D.ambient).integralPoints ≤ L →
          L = (IntegralModelCompletions.canonicalModel F S v D.ambient).integralPoints) :
    ModelLocalConditions F G P p S D.ambient :=
  ModelLocalConditions.of_canonicalModels F G P p S D.ambient hmax
    (canonicalModel_covering F S hQ D)

end Langlands.Global.IntegralIwasawaFamily
