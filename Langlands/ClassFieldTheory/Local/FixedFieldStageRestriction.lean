import Langlands.ClassFieldTheory.Local.FixedFieldStages
import Langlands.Cohomology.Continuous.QuotientSubgroupCohomology

noncomputable section

open CategoryTheory
open Langlands.Continuous

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace Langlands.ClassFieldTheory.Local

universe u

section Algebraic

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) (N : ClosedSubgroup Gal(L/K)) [N.Normal]

omit [IsGalois K L] [N.Normal] in
/-- Subgroup containment gives the actual intermediate-field inclusion. -/
theorem le_fixedField_of_le_fixingSubgroup (h : N.toSubgroup ≤ E.fixingSubgroup) :
    E ≤ IntermediateField.fixedField N.toSubgroup :=
  (IntermediateField.le_iff_le N.toSubgroup E).mpr h

/-- The algebra structure induced by the actual inclusion into the fixed field. -/
abbrev fixedFieldRestrictedAlgebra (h : N.toSubgroup ≤ E.fixingSubgroup) :
    Algebra E (IntermediateField.fixedField N.toSubgroup) :=
  (IntermediateField.inclusion (le_fixedField_of_le_fixingSubgroup K L E N h)).toRingHom.toAlgebra

omit [IsGalois K L] [N.Normal] in
/-- The inclusion algebra agrees with the base-field algebra maps. -/
theorem fixedFieldRestrictedTowerBase (h : N.toSubgroup ≤ E.fixingSubgroup) :
    letI := fixedFieldRestrictedAlgebra K L E N h
    IsScalarTower K E (IntermediateField.fixedField N.toSubgroup) := by
  let := fixedFieldRestrictedAlgebra K L E N h
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [IsGalois K L] [N.Normal] in
/-- Both inclusions into the ambient field form the canonical scalar tower. -/
theorem fixedFieldRestrictedTowerTop (h : N.toSubgroup ≤ E.fixingSubgroup) :
    letI := fixedFieldRestrictedAlgebra K L E N h
    IsScalarTower E (IntermediateField.fixedField N.toSubgroup) L := by
  let := fixedFieldRestrictedAlgebra K L E N h
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

variable [Algebra E (IntermediateField.fixedField N.toSubgroup)]
  [IsScalarTower K E (IntermediateField.fixedField N.toSubgroup)]
  [IsScalarTower E (IntermediateField.fixedField N.toSubgroup) L]

/-- Restriction of an automorphism fixing `E` to the fixed field of `N`. -/
def fixedFieldRestrictedGroupHom :
    E.fixingSubgroup →* Gal(IntermediateField.fixedField N.toSubgroup/E) := by
  let : Normal E (IntermediateField.fixedField N.toSubgroup) :=
    Normal.tower_top_of_normal K E (IntermediateField.fixedField N.toSubgroup)
  exact (AlgEquiv.restrictNormalHom (IntermediateField.fixedField N.toSubgroup)).comp
    (IntermediateField.fixingSubgroupEquiv E).toMonoidHom

/-- Every automorphism over `E` of the fixed field extends to the ambient Galois field. -/
theorem fixedFieldRestrictedGroupHom_surjective :
    Function.Surjective (fixedFieldRestrictedGroupHom K L E N) := by
  let : Normal E (IntermediateField.fixedField N.toSubgroup) :=
    Normal.tower_top_of_normal K E (IntermediateField.fixedField N.toSubgroup)
  exact (AlgEquiv.restrictNormalHom_surjective L).comp
    (IntermediateField.fixingSubgroupEquiv E).surjective

/-- The kernel is exactly the pullback of `N` to the fixing subgroup of `E`. -/
theorem fixedFieldRestrictedGroupHom_ker :
    N.toSubgroup.comap E.fixingSubgroup.subtype =
      (fixedFieldRestrictedGroupHom K L E N).ker := by
  ext σ
  change σ.1 ∈ N.toSubgroup ↔ fixedFieldRestrictedGroupHom K L E N σ = 1
  let : Normal E (IntermediateField.fixedField N.toSubgroup) :=
    Normal.tower_top_of_normal K E (IntermediateField.fixedField N.toSubgroup)
  constructor
  · intro h
    have hf : σ.1 ∈ (IntermediateField.fixedField N.toSubgroup).fixingSubgroup := by
      simpa only [InfiniteGalois.fixingSubgroup_fixedField N] using h
    apply AlgEquiv.ext
    intro x
    apply (algebraMap (IntermediateField.fixedField N.toSubgroup) L).injective
    exact ((IntermediateField.fixingSubgroupEquiv E σ).restrictNormal_commutes (IntermediateField.fixedField N.toSubgroup) x).trans
      (hf x)
  · intro h
    rw [← InfiniteGalois.fixingSubgroup_fixedField N]
    intro x
    have hx := congrArg (fun τ : Gal(IntermediateField.fixedField N.toSubgroup/E) => algebraMap (IntermediateField.fixedField N.toSubgroup) L (τ x)) h
    exact ((IntermediateField.fixingSubgroupEquiv E σ).restrictNormal_commutes (IntermediateField.fixedField N.toSubgroup) x).symm.trans hx

/-- The actual subgroup quotient is the automorphism group of the fixed field over `E`. -/
def fixedFieldRestrictedGroupEquiv :
    E.fixingSubgroup ⧸ N.toSubgroup.comap E.fixingSubgroup.subtype ≃* Gal(IntermediateField.fixedField N.toSubgroup/E) :=
  QuotientGroup.liftEquiv _ (fixedFieldRestrictedGroupHom_surjective K L E N)
    (fixedFieldRestrictedGroupHom_ker K L E N)

/-- The relative group equivalence is compatible with inclusion in the ambient quotient. -/
theorem fixedFieldRestrictedGroupEquiv_commutes :
    (InfiniteGalois.normalAutEquivQuotient N).toMonoidHom.comp
        (quotientSubgroupMap E.fixingSubgroup N.toSubgroup) =
      (AlgEquiv.restrictScalarsHom K).comp
        (fixedFieldRestrictedGroupEquiv K L E N).toMonoidHom := by
  let : Normal E (IntermediateField.fixedField N.toSubgroup) :=
    Normal.tower_top_of_normal K E (IntermediateField.fixedField N.toSubgroup)
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x (fun σ => ?_)
  apply AlgEquiv.ext
  intro y
  apply (algebraMap (IntermediateField.fixedField N.toSubgroup) L).injective
  exact (σ.1.restrictNormal_commutes (IntermediateField.fixedField N.toSubgroup) y).trans
    ((IntermediateField.fixingSubgroupEquiv E σ).restrictNormal_commutes (IntermediateField.fixedField N.toSubgroup) y).symm

/-- The coefficient equivalence retains the underlying unit of the ambient field. -/
def fixedFieldRestrictedUnitsEquiv (h : N.toSubgroup ≤ E.fixingSubgroup) :
    Representation.invariants
        (((unitsRepresentation K L).ρ.comp E.fixingSubgroup.subtype).comp
          (N.toSubgroup.comap E.fixingSubgroup.subtype).subtype) ≃ₗ[IntegerScalars.{u}]
      Additive (IntermediateField.fixedField N.toSubgroup)ˣ :=
  (fixedRestrictionEquiv (unitsRepresentation K L) E.fixingSubgroup N.toSubgroup h).symm.trans
    (fixedFieldUnitsLinearEquiv K L N.toSubgroup)

/-- The coefficient and group identifications respect the actual quotient action. -/
theorem fixedFieldRestrictedUnitsEquiv_intertwines (h : N.toSubgroup ≤ E.fixingSubgroup)
    (g : E.fixingSubgroup ⧸ N.toSubgroup.comap E.fixingSubgroup.subtype) :
    (fixedFieldRestrictedUnitsEquiv K L E N h).toLinearMap ∘ₗ
        ((Rep.res E.fixingSubgroup.subtype (unitsRepresentation K L)).quotientToInvariants
          (N.toSubgroup.comap E.fixingSubgroup.subtype)).ρ g =
      (unitsRepresentation E (IntermediateField.fixedField N.toSubgroup)).ρ (fixedFieldRestrictedGroupEquiv K L E N g) ∘ₗ
        (fixedFieldRestrictedUnitsEquiv K L E N h).toLinearMap := by
  let : Normal E (IntermediateField.fixedField N.toSubgroup) :=
    Normal.tower_top_of_normal K E (IntermediateField.fixedField N.toSubgroup)
  refine QuotientGroup.induction_on g (fun σ => ?_)
  apply LinearMap.ext
  intro x
  apply Units.ext
  apply Subtype.ext
  exact ((IntermediateField.fixingSubgroupEquiv E σ).restrictNormal_commutes (IntermediateField.fixedField N.toSubgroup)
    (fixedFieldRestrictedUnitsEquiv K L E N h x).toMul.val).symm

/-- Subgroup finite-stage cohomology is the relative cohomology of the fixed field. -/
def fixedFieldRestrictedCohomologyIso (h : N.toSubgroup ≤ E.fixingSubgroup) (q : ℕ) :
    groupCohomology
        ((Rep.res E.fixingSubgroup.subtype (unitsRepresentation K L)).quotientToInvariants
          (N.toSubgroup.comap E.fixingSubgroup.subtype)) q ≅ relativeCohomology E (IntermediateField.fixedField N.toSubgroup) q :=
  groupCohomology.mapIso (fixedFieldRestrictedGroupEquiv K L E N)
    (fixedFieldRestrictedUnitsEquiv K L E N h)
    (fixedFieldRestrictedUnitsEquiv_intertwines K L E N h) q

/-- Intrinsic quotient restriction is the unchanged relative field restriction. -/
theorem fixedFieldRestrictedCohomologyIso_restriction
    (h : N.toSubgroup ≤ E.fixingSubgroup) (q : ℕ) :
    groupCohomology.map (quotientSubgroupMap E.fixingSubgroup N.toSubgroup)
        (fixedSubgroupRestriction (unitsRepresentation K L) E.fixingSubgroup N.toSubgroup) q ≫
      (fixedFieldRestrictedCohomologyIso K L E N h q).hom =
        (fixedFieldCohomologyIso K L N q).hom ≫
          relativeRestriction K E (IntermediateField.fixedField N.toSubgroup) q := by
  unfold fixedFieldRestrictedCohomologyIso fixedFieldCohomologyIso
  rw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro σ
    apply (InfiniteGalois.normalAutEquivQuotient N).injective
    have hc := DFunLike.congr_fun (fixedFieldRestrictedGroupEquiv_commutes K L E N)
      ((fixedFieldRestrictedGroupEquiv K L E N).symm σ)
    simpa using hc
  · rfl

end Algebraic

section FiniteStages

variable (K : Type u) [Field K] [CharZero K]
  (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
  (h : N.toSubgroup ≤ (finiteGaloisFixingSubgroup K E).toSubgroup)

omit [CharZero K] [FiniteDimensional K E] [IsGalois K E] in
/-- The subgroup bound produces the actual inclusion in the finite-stage fixed field. -/
theorem finiteStageFixedField_contains (h : N.toSubgroup ≤ E.fixingSubgroup) :
    E ≤ finiteStageFixedField K N :=
  le_fixedField_of_le_fixingSubgroup K (AlgebraicClosure K) E
    (finiteStageClosedSubgroup K N) h

/-- The canonical algebra structure associated to this intermediate-field inclusion. -/
abbrev finiteStageRestrictedAlgebra : Algebra E (finiteStageFixedField K N) :=
  fixedFieldRestrictedAlgebra K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h

/-- The base field, intermediate field, and finite-stage field form the canonical tower. -/
theorem finiteStageRestrictedTowerBase :
    letI := finiteStageRestrictedAlgebra K E N h
    IsScalarTower K E (finiteStageFixedField K N) :=
  fixedFieldRestrictedTowerBase K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h

/-- The two canonical inclusions into the algebraic closure form a scalar tower. -/
theorem finiteStageRestrictedTowerTop :
    letI := finiteStageRestrictedAlgebra K E N h
    IsScalarTower E (finiteStageFixedField K N) (AlgebraicClosure K) :=
  fixedFieldRestrictedTowerTop K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h

/-- The actual target of finite restriction identifies with relative fixed-field cohomology. -/
def finiteStageRestrictedRelativeIso (q : ℕ) :
    letI := finiteStageRestrictedAlgebra K E N h
    groupCohomology
        (finiteQuotientRep
          ((absoluteUnitDiscreteModule K).restrict (finiteGaloisFixingSubgroup K E).toSubgroup).toRep
          (restrictOpenNormal (finiteGaloisFixingSubgroup K E).toOpenSubgroup N)) q ≅
      relativeCohomology E (finiteStageFixedField K N) q := by
  letI := fixedFieldRestrictedAlgebra K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h
  letI := fixedFieldRestrictedTowerBase K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h
  letI := fixedFieldRestrictedTowerTop K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h
  exact fixedFieldRestrictedCohomologyIso K (AlgebraicClosure K) E
    (finiteStageClosedSubgroup K N) h q

/-- Finite-stage restriction is the unchanged relative restriction under the canonical comparisons. -/
theorem finiteStageRelativeIso_restriction (q : ℕ) :
    letI := finiteStageRestrictedAlgebra K E N h
    letI := finiteStageRestrictedTowerBase K E N h
    finiteRestriction (absoluteUnitDiscreteModule K)
        (finiteGaloisFixingSubgroup K E).toOpenSubgroup N q ≫
      (finiteStageRestrictedRelativeIso K E N h q).hom =
        (finiteStageRelativeIso K N q).hom ≫
          relativeRestriction K E (finiteStageFixedField K N) q := by
  let := fixedFieldRestrictedAlgebra K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h
  let := fixedFieldRestrictedTowerBase K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h
  let := fixedFieldRestrictedTowerTop K (AlgebraicClosure K) E (finiteStageClosedSubgroup K N) h
  exact fixedFieldRestrictedCohomologyIso_restriction K (AlgebraicClosure K) E
    (finiteStageClosedSubgroup K N) h q

end FiniteStages

end Langlands.ClassFieldTheory.Local
