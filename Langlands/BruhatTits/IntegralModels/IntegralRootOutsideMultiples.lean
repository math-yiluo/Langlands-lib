import Langlands.BruhatTits.IntegralModels.IntegralRootQuotientLifting
import Langlands.BruhatTits.IntegralModels.IntegralRootReduction
import Langlands.GroupScheme.Rational.RootPointOutsideMultiples

/-! # Integral root points outside higher-multiple root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

open GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

include hT hQ in
/-- An actual quotient root has an integral generic-root witness outside
every specified higher multiple, both generically and in quotient reduction. -/
theorem exists_integral_root_point_outside_nsmul
    {a : characterLattice S}
    (ha : T.characterSpecialization hT a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection))
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : D.neutral.integralSections,
      D.neutral.integralPointMap x ∈ rootGroupPoints i a ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∈
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (T.characterSpecialization hT a)).carrier _ ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∉
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (n • T.characterSpecialization hT a)).carrier _ ∧
      D.neutral.integralPointMap x ∉ rootGroupPoints i (n • a) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hs := hT.baseChange (IntegralModel.residueBaseMap R)
  have ha0 : a ≠ 0 := by
    intro hz
    apply ha.1
    rw [hz, map_zero]
  have hna0 : n • a ≠ 0 := by
    intro hz
    apply hs.nsmul_ne_zero ha.1 (show n ≠ 0 by omega)
    rw [← map_nsmul, hz, map_zero]
  obtain ⟨g, hg, hgn⟩ := RelativeRoot.exists_rootPoint_not_mem_nsmul
    hs (T.specialFibreInclusion ≫ Q.projection) ha hn
  obtain ⟨x, hx, hxg⟩ :=
    T.exists_integral_root_quotient_lift hT Q hQ a ha0 g hg
  refine ⟨x, hx, hxg.symm ▸ hg, hxg.symm ▸ hgn, ?_⟩
  intro hxn
  have hr := T.quotient_reduction_mem_rootFunctor hT Q (n • a) hna0 x hxn
  rw [map_nsmul, hxg] at hr
  exact hgn hr

/-- Choose an integral point with exact generic root membership and
higher-multiple exclusion both generically and in the actual quotient. -/
def integralRootPointOutsideMultiple
    {a : characterLattice S}
    (ha : T.characterSpecialization hT a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection))
    {n : ℕ} (hn : 2 ≤ n) :
    {x : D.neutral.integralSections //
      D.neutral.integralPointMap x ∈ rootGroupPoints i a ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∈
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (T.characterSpecialization hT a)).carrier _ ∧
      rationalPoints.map Q.projection (D.neutral.reduction x) ∉
        (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
          (n • T.characterSpecialization hT a)).carrier _ ∧
      D.neutral.integralPointMap x ∉ rootGroupPoints i (n • a)} :=
  ⟨Classical.choose (T.exists_integral_root_point_outside_nsmul hT Q hQ ha hn),
    Classical.choose_spec (T.exists_integral_root_point_outside_nsmul hT Q hQ ha hn)⟩

end Langlands.BruhatTits.IntegralModels.IntegralTorusData
