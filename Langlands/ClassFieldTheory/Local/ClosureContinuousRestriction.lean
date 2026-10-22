import Langlands.ClassFieldTheory.Local.ClosureCohomologyTransport
import Langlands.ClassFieldTheory.Local.FixedFieldStages

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K]

section Bridge

variable (E : IntermediateField K (AlgebraicClosure K))

set_option backward.isDefEq.respectTransparency false in
/-- The transport's restriction map is the Library's actual restriction of the discrete
closure-unit module to the fixing subgroup. -/
theorem closureSubgroupRestriction_eq_continuousRestriction (q : ℕ) :
    closureSubgroupRestriction K E q =
      continuousRestriction (absoluteUnitDiscreteModule K) E.fixingSubgroup q := rfl

end Bridge

variable [CharZero K]

section FixingSubgroup

variable (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]

set_option backward.isDefEq.respectTransparency false in
/-- Actual restriction to the fixing subgroup, followed by transport, is absolute restriction. -/
theorem continuousRestriction_comp_closureSubgroupCohomologyMap (q : ℕ) :
    continuousRestriction (absoluteUnitDiscreteModule K) E.fixingSubgroup q ≫
        closureSubgroupCohomologyMap K E q =
      absoluteRestriction K E q :=
  closureSubgroupRestriction_comp K E q

set_option backward.isDefEq.respectTransparency false in
/-- The same identity on elements, for the continuous linear equivalence. -/
theorem closureSubgroupCohomologyEquiv_continuousRestriction (q : ℕ)
    (x : absoluteCohomology K q) :
    closureSubgroupCohomologyEquiv K E q
        (continuousRestriction (absoluteUnitDiscreteModule K) E.fixingSubgroup q x) =
      absoluteRestriction K E q x :=
  closureSubgroupCohomologyEquiv_restriction K E q x

set_option backward.isDefEq.respectTransparency false in
/-- A class dies under absolute restriction iff it dies on the actual fixing subgroup. -/
theorem absoluteRestriction_eq_zero_iff_continuousRestriction (q : ℕ)
    (x : absoluteCohomology K q) :
    absoluteRestriction K E q x = 0 ↔
      continuousRestriction (absoluteUnitDiscreteModule K) E.fixingSubgroup q x = 0 :=
  absoluteRestriction_eq_zero_iff_subgroup K E q x

set_option backward.isDefEq.respectTransparency false in
/-- Absolute restriction and actual subgroup restriction have the same kernel. -/
theorem absoluteRestriction_ker_eq_continuousRestriction_ker (q : ℕ) :
    LinearMap.ker (absoluteRestriction K E q).hom.toLinearMap =
      LinearMap.ker (continuousRestriction (absoluteUnitDiscreteModule K) E.fixingSubgroup
        q).hom.toLinearMap :=
  absoluteRestriction_ker_eq_subgroup K E q

end FixingSubgroup

section FiniteGalois

variable (E : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K E] [IsGalois K E]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]

/-- The transport isomorphism at the bundled open normal fixing subgroup of `E`. -/
def finiteGaloisFixingCohomologyIso (q : ℕ) :
    continuousCohomology q ((absoluteUnitDiscreteModule K).restrict
        (finiteGaloisFixingSubgroup K E).toSubgroup).toTopRep ≅
      absoluteCohomology E q :=
  closureSubgroupCohomologyIso K E q

/-- Its forward map is the actual transport map. -/
theorem finiteGaloisFixingCohomologyIso_hom (q : ℕ) :
    (finiteGaloisFixingCohomologyIso K E q).hom = closureSubgroupCohomologyMap K E q :=
  closureSubgroupCohomologyIso_hom K E q

/-- The same identification as a continuous linear equivalence. -/
def finiteGaloisFixingCohomologyEquiv (q : ℕ) :
    continuousCohomology q ((absoluteUnitDiscreteModule K).restrict
        (finiteGaloisFixingSubgroup K E).toSubgroup).toTopRep ≃L[IntegerScalars.{u}]
      absoluteCohomology E q :=
  (finiteGaloisFixingCohomologyIso K E q).toContinuousLinearEquiv

/-- The same identification as an additive equivalence. -/
def finiteGaloisFixingCohomologyAddEquiv (q : ℕ) :
    continuousCohomology q ((absoluteUnitDiscreteModule K).restrict
        (finiteGaloisFixingSubgroup K E).toSubgroup).toTopRep ≃+
      absoluteCohomology E q :=
  (finiteGaloisFixingCohomologyEquiv K E q).toLinearEquiv.toAddEquiv

/-- Actual restriction to the open normal fixing subgroup, then transport, is absolute
restriction. -/
theorem continuousRestriction_comp_finiteGaloisFixingCohomologyIso (q : ℕ) :
    continuousRestriction (absoluteUnitDiscreteModule K)
        (finiteGaloisFixingSubgroup K E).toSubgroup q ≫
        (finiteGaloisFixingCohomologyIso K E q).hom =
      absoluteRestriction K E q :=
  closureSubgroupRestriction_comp K E q

/-- The pointwise identity for the continuous linear equivalence. -/
theorem finiteGaloisFixingCohomologyEquiv_continuousRestriction (q : ℕ)
    (x : absoluteCohomology K q) :
    finiteGaloisFixingCohomologyEquiv K E q
        (continuousRestriction (absoluteUnitDiscreteModule K)
          (finiteGaloisFixingSubgroup K E).toSubgroup q x) =
      absoluteRestriction K E q x :=
  closureSubgroupCohomologyEquiv_restriction K E q x

/-- The pointwise identity for the additive equivalence. -/
theorem finiteGaloisFixingCohomologyAddEquiv_continuousRestriction (q : ℕ)
    (x : absoluteCohomology K q) :
    finiteGaloisFixingCohomologyAddEquiv K E q
        (continuousRestriction (absoluteUnitDiscreteModule K)
          (finiteGaloisFixingSubgroup K E).toSubgroup q x) =
      absoluteRestriction K E q x :=
  closureSubgroupCohomologyEquiv_restriction K E q x

/-- Vanishing under absolute restriction is detected on the open normal fixing subgroup. -/
theorem absoluteRestriction_eq_zero_iff_finiteGaloisFixing (q : ℕ)
    (x : absoluteCohomology K q) :
    absoluteRestriction K E q x = 0 ↔
      continuousRestriction (absoluteUnitDiscreteModule K)
        (finiteGaloisFixingSubgroup K E).toSubgroup q x = 0 :=
  absoluteRestriction_eq_zero_iff_subgroup K E q x

/-- Absolute restriction and restriction to the open normal fixing subgroup have the same
kernel. -/
theorem absoluteRestriction_ker_eq_finiteGaloisFixing_ker (q : ℕ) :
    LinearMap.ker (absoluteRestriction K E q).hom.toLinearMap =
      LinearMap.ker (continuousRestriction (absoluteUnitDiscreteModule K)
        (finiteGaloisFixingSubgroup K E).toSubgroup q).hom.toLinearMap :=
  absoluteRestriction_ker_eq_subgroup K E q

/-- The same kernel equality for the underlying additive maps. -/
theorem absoluteRestriction_addMonoidHom_ker_eq_finiteGaloisFixing_ker (q : ℕ) :
    (absoluteRestriction K E q).hom.toAddMonoidHom.ker =
      (continuousRestriction (absoluteUnitDiscreteModule K)
        (finiteGaloisFixingSubgroup K E).toSubgroup q).hom.toAddMonoidHom.ker := by
  ext x
  exact absoluteRestriction_eq_zero_iff_finiteGaloisFixing K E q x

end FiniteGalois

end Langlands.ClassFieldTheory.Local
