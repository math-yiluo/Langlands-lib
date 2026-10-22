import Langlands.ClassFieldTheory.Local.ClosureUnitTransport
import Langlands.Cohomology.Continuous.EquivalenceTransport

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K] [CharZero K]
variable (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]

set_option backward.isDefEq.respectTransparency false in
/-- Actual continuous cohomology restriction to the fixing subgroup. -/
def closureSubgroupRestriction (q : ℕ) :
    absoluteCohomology K q ⟶
      continuousCohomology q (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K)) :=
  ContinuousCohomology.map
    (Langlands.Continuous.subgroupInclusion (G := Field.absoluteGaloisGroup K) E.fixingSubgroup)
    (𝟙 (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K))) q

set_option backward.isDefEq.respectTransparency false in
/-- The actual continuous cohomology transport map, using the supplied closure inclusion. -/
def closureSubgroupCohomologyMap (q : ℕ) :
    continuousCohomology q (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K)) ⟶
      absoluteCohomology E q :=
  ContinuousCohomology.map (closureSubgroupMap K E) (closureSubgroupCoefficientsIso K E).hom q

set_option backward.isDefEq.respectTransparency false in
/-- Group and coefficient equivalences induce an isomorphism in every degree. -/
def closureSubgroupCohomologyIso (q : ℕ) :
    continuousCohomology q (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K)) ≅
      absoluteCohomology E q :=
  Langlands.Continuous.continuousCohomologyIso (closureSubgroupEquiv K E)
    (closureSubgroupCoefficientsIso K E) q

@[simp]
theorem closureSubgroupCohomologyIso_hom (q : ℕ) :
    (closureSubgroupCohomologyIso K E q).hom = closureSubgroupCohomologyMap K E q := rfl

/-- The transport as a continuous linear equivalence of the actual cohomology modules. -/
def closureSubgroupCohomologyEquiv (q : ℕ) :
    continuousCohomology q (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K))
      ≃L[IntegerScalars.{u}] absoluteCohomology E q :=
  (closureSubgroupCohomologyIso K E q).toContinuousLinearEquiv

@[simp]
theorem closureSubgroupCohomologyEquiv_apply (q : ℕ)
    (x : continuousCohomology q (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K))) :
    closureSubgroupCohomologyEquiv K E q x = (closureSubgroupCohomologyMap K E q).hom x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The subgroup-restriction square is the original absolute restriction in every degree. -/
theorem closureSubgroupRestriction_comp (q : ℕ) :
    closureSubgroupRestriction K E q ≫ closureSubgroupCohomologyMap K E q =
      absoluteRestriction K E q := by
  unfold closureSubgroupRestriction closureSubgroupCohomologyMap
  rw [← ContinuousCohomology.map_comp]
  rfl

/-- Pointwise comparison with the continuous linear equivalence. -/
theorem closureSubgroupCohomologyEquiv_restriction (q : ℕ) (x : absoluteCohomology K q) :
    closureSubgroupCohomologyEquiv K E q ((closureSubgroupRestriction K E q).hom x) =
      (absoluteRestriction K E q).hom x :=
  congrArg (fun f => f.hom x) (closureSubgroupRestriction_comp K E q)

/-- Absolute restriction vanishes exactly when actual fixing-subgroup restriction vanishes. -/
theorem absoluteRestriction_eq_zero_iff_subgroup (q : ℕ) (x : absoluteCohomology K q) :
    (absoluteRestriction K E q).hom x = 0 ↔ (closureSubgroupRestriction K E q).hom x = 0 := by
  rw [← closureSubgroupCohomologyEquiv_restriction]
  exact (closureSubgroupCohomologyEquiv K E q).map_eq_zero_iff

/-- The two actual restriction maps have the same kernel, without a further premise. -/
theorem absoluteRestriction_ker_eq_subgroup (q : ℕ) :
    LinearMap.ker (absoluteRestriction K E q).hom.toLinearMap =
      LinearMap.ker (closureSubgroupRestriction K E q).hom.toLinearMap := by
  ext x
  exact absoluteRestriction_eq_zero_iff_subgroup K E q x

end Langlands.ClassFieldTheory.Local
