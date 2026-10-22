import Langlands.ClassFieldTheory.Local.FixedFieldStages

noncomputable section

open CategoryTheory Langlands.Continuous

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

namespace FixedFieldRefinement

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- Regard an open normal subgroup as the closed subgroup needed for Galois descent. -/
abbrev closed (N : OpenNormalSubgroup Gal(L/K)) : ClosedSubgroup Gal(L/K) :=
  ⟨N.toSubgroup, N.toOpenSubgroup.isClosed⟩

instance (N : OpenNormalSubgroup Gal(L/K)) : (closed K L N).Normal := N.isNormal'

variable {K L} {N M : OpenNormalSubgroup Gal(L/K)} (h : N ≤ M)

omit [IsGalois K L] in
/-- Refinement of subgroups reverses to inclusion of their fixed fields. -/
theorem fixedField_le (h : N ≤ M) :
    IntermediateField.fixedField M.toSubgroup ≤ IntermediateField.fixedField N.toSubgroup :=
  IntermediateField.fixedField_le h

/-- The inclusion is the actual inclusion of intermediate fields. -/
abbrev fieldInclusion :
    IntermediateField.fixedField M.toSubgroup →ₐ[K]
      IntermediateField.fixedField N.toSubgroup :=
  IntermediateField.inclusion (fixedField_le h)

/-- The algebra structure used by relative inflation is induced by field inclusion. -/
abbrev inclusionAlgebra :
    Algebra (IntermediateField.fixedField M.toSubgroup)
      (IntermediateField.fixedField N.toSubgroup) :=
  (fieldInclusion h).toRingHom.toAlgebra

/-- The inclusion commutes with the base-field algebra maps. -/
instance baseTower :
    letI := inclusionAlgebra h
    IsScalarTower K (IntermediateField.fixedField M.toSubgroup)
      (IntermediateField.fixedField N.toSubgroup) :=
  IsScalarTower.of_algHom (fieldInclusion h)

/-- Both fixed-field inclusions into the ambient field form a scalar tower. -/
instance ambientTower :
    letI := inclusionAlgebra h
    IsScalarTower (IntermediateField.fixedField M.toSubgroup)
      (IntermediateField.fixedField N.toSubgroup) L :=
  letI := inclusionAlgebra h
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Quotient transition corresponds to restriction of fixed-field automorphisms. -/
lemma quotient_restriction (g : Gal(L/K) ⧸ N.toSubgroup) :
    letI := inclusionAlgebra h
    InfiniteGalois.normalAutEquivQuotient (closed K L M) (quotientTransition h g) =
      (InfiniteGalois.normalAutEquivQuotient (closed K L N) g).restrictNormal
        (IntermediateField.fixedField M.toSubgroup) := by
  let := inclusionAlgebra h
  let := baseTower h
  let := ambientTower h
  induction g using QuotientGroup.induction_on with
  | H σ =>
    exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
      (IntermediateField.fixedField M.toSubgroup)
      (IntermediateField.fixedField N.toSubgroup) σ

/-- The inverse quotient identifications give the group maps used by cohomology. -/
lemma quotient_restriction_symm :
    letI := inclusionAlgebra h
    (quotientTransition h).comp
        (InfiniteGalois.normalAutEquivQuotient (closed K L N)).symm.toMonoidHom =
      (InfiniteGalois.normalAutEquivQuotient (closed K L M)).symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom (IntermediateField.fixedField M.toSubgroup)) := by
  let := inclusionAlgebra h
  let := baseTower h
  ext σ
  apply (InfiniteGalois.normalAutEquivQuotient (closed K L M)).injective
  simpa [AlgEquiv.restrictNormalHom] using quotient_restriction h
    ((InfiniteGalois.normalAutEquivQuotient (closed K L N)).symm σ)

/-- Fixed-unit cohomology identification carries finite inflation to relative inflation. -/
lemma cohomology_inflation (q : ℕ) :
    letI := inclusionAlgebra h
    letI := baseTower h
    finiteInflation (unitsRepresentation K L) q h ≫
        (fixedFieldCohomologyIso K L (closed K L N) q).hom =
      (fixedFieldCohomologyIso K L (closed K L M) q).hom ≫
        relativeInflation K (IntermediateField.fixedField M.toSubgroup)
          (IntermediateField.fixedField N.toSubgroup) q := by
  let := inclusionAlgebra h
  let := baseTower h
  rw [finiteInflation, fixedFieldCohomologyIso, fixedFieldCohomologyIso,
    groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (quotient_restriction_symm h)
  apply LinearMap.ext
  intro x
  apply Units.ext
  apply Subtype.ext
  rfl

end FixedFieldRefinement

variable (K : Type u) [Field K] [CharZero K]
  {N M : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}

omit [CharZero K] in
/-- Absolute finite-stage refinement reverses to inclusion of the fixed fields. -/
theorem finiteStageFixedField_le (h : N ≤ M) :
    finiteStageFixedField K M ≤ finiteStageFixedField K N :=
  FixedFieldRefinement.fixedField_le h

/-- The actual field inclusion associated to absolute finite-stage refinement. -/
def finiteStageFieldInclusion (h : N ≤ M) :
    finiteStageFixedField K M →ₐ[K] finiteStageFixedField K N :=
  IntermediateField.inclusion (finiteStageFixedField_le K h)

/-- The algebra structure induced by the absolute finite-stage field inclusion. -/
abbrev finiteStageInclusionAlgebra (h : N ≤ M) :
    Algebra (finiteStageFixedField K M) (finiteStageFixedField K N) :=
  (finiteStageFieldInclusion K h).toRingHom.toAlgebra

instance finiteStageBaseTower (h : N ≤ M) :
    letI := finiteStageInclusionAlgebra K h
    IsScalarTower K (finiteStageFixedField K M) (finiteStageFixedField K N) :=
  IsScalarTower.of_algHom (finiteStageFieldInclusion K h)

instance finiteStageAmbientTower (h : N ≤ M) :
    letI := finiteStageInclusionAlgebra K h
    IsScalarTower (finiteStageFixedField K M) (finiteStageFixedField K N)
      (AlgebraicClosure K) :=
  letI := finiteStageInclusionAlgebra K h
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The absolute finite-stage identification carries refinement to relative inflation. -/
theorem finiteStageRelativeIso_inflation (q : ℕ) (h : N ≤ M) :
    letI := finiteStageInclusionAlgebra K h
    letI := finiteStageBaseTower K h
    finiteInflation (absoluteUnitDiscreteModule K).toRep q h ≫
        (finiteStageRelativeIso K N q).hom =
      (finiteStageRelativeIso K M q).hom ≫
        relativeInflation K (finiteStageFixedField K M) (finiteStageFixedField K N) q :=
  FixedFieldRefinement.cohomology_inflation h q

variable (E : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K E] [IsGalois K E]

/-- A stage refining the fixing subgroup of `E` contains `E` itself. -/
theorem finiteGaloisStage_le (h : N ≤ finiteGaloisFixingSubgroup K E) :
    E ≤ finiteStageFixedField K N := by
  rw [← finiteStageFixedField_finiteGaloisFixingSubgroup K E]
  exact finiteStageFixedField_le K h

/-- The actual inclusion of the specified finite Galois field into a refining stage. -/
def finiteGaloisStageFieldInclusion (h : N ≤ finiteGaloisFixingSubgroup K E) :
    E →ₐ[K] finiteStageFixedField K N :=
  IntermediateField.inclusion (finiteGaloisStage_le K E h)

abbrev finiteGaloisStageInclusionAlgebra (h : N ≤ finiteGaloisFixingSubgroup K E) :
    Algebra E (finiteStageFixedField K N) :=
  (finiteGaloisStageFieldInclusion K E h).toRingHom.toAlgebra

instance finiteGaloisStageBaseTower (h : N ≤ finiteGaloisFixingSubgroup K E) :
    letI := finiteGaloisStageInclusionAlgebra K E h
    IsScalarTower K E (finiteStageFixedField K N) :=
  IsScalarTower.of_algHom (finiteGaloisStageFieldInclusion K E h)

instance finiteGaloisStageAmbientTower (h : N ≤ finiteGaloisFixingSubgroup K E) :
    letI := finiteGaloisStageInclusionAlgebra K E h
    IsScalarTower E (finiteStageFixedField K N) (AlgebraicClosure K) :=
  letI := finiteGaloisStageInclusionAlgebra K E h
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Quotient transition to the fixing subgroup of `E` is restriction to `E`. -/
lemma finiteGaloisStage_quotient_restriction
    (h : N ≤ finiteGaloisFixingSubgroup K E)
    (g : Field.absoluteGaloisGroup K ⧸ N.toSubgroup) :
    letI := finiteGaloisStageInclusionAlgebra K E h
    finiteGaloisStageGroupEquiv K E (quotientTransition h g) =
      (InfiniteGalois.normalAutEquivQuotient
        (FixedFieldRefinement.closed K (AlgebraicClosure K) N) g).restrictNormal E := by
  let := finiteGaloisStageInclusionAlgebra K E h
  let := finiteGaloisStageBaseTower K E h
  let := finiteGaloisStageAmbientTower K E h
  induction g using QuotientGroup.induction_on with
  | H σ =>
    exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E
      (finiteStageFixedField K N) σ

/-- Inverse group identifications give the same restriction homomorphism. -/
lemma finiteGaloisStage_quotient_restriction_symm
    (h : N ≤ finiteGaloisFixingSubgroup K E) :
    letI := finiteGaloisStageInclusionAlgebra K E h
    (quotientTransition h).comp
        (InfiniteGalois.normalAutEquivQuotient
          (FixedFieldRefinement.closed K (AlgebraicClosure K) N)).symm.toMonoidHom =
      (finiteGaloisStageGroupEquiv K E).symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom E) := by
  let := finiteGaloisStageInclusionAlgebra K E h
  let := finiteGaloisStageBaseTower K E h
  ext σ
  apply (finiteGaloisStageGroupEquiv K E).injective
  have hs := finiteGaloisStage_quotient_restriction K E h
    ((InfiniteGalois.normalAutEquivQuotient
      (FixedFieldRefinement.closed K (AlgebraicClosure K) N)).symm σ)
  simp only [MulEquiv.apply_symm_apply] at hs
  convert hs using 1 <;> first
  | rfl
  | exact (finiteGaloisStageGroupEquiv K E).apply_symm_apply (σ.restrictNormal E)

/-- The direct identification at `E` carries refinement to inflation from `E`. -/
theorem finiteGaloisStageRelativeIso_inflation (q : ℕ)
    (h : N ≤ finiteGaloisFixingSubgroup K E) :
    letI := finiteGaloisStageInclusionAlgebra K E h
    letI := finiteGaloisStageBaseTower K E h
    finiteInflation (absoluteUnitDiscreteModule K).toRep q h ≫
        (finiteStageRelativeIso K N q).hom =
      (finiteGaloisStageRelativeIso K E q).hom ≫
        relativeInflation K E (finiteStageFixedField K N) q := by
  let := finiteGaloisStageInclusionAlgebra K E h
  let := finiteGaloisStageBaseTower K E h
  rw [finiteInflation, finiteStageRelativeIso, fixedFieldCohomologyIso,
    finiteGaloisStageRelativeIso, groupCohomology.mapIso_hom,
    groupCohomology.mapIso_hom, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (finiteGaloisStage_quotient_restriction_symm K E h)
  apply LinearMap.ext
  intro x
  apply Units.ext
  apply Subtype.ext
  rfl

end Langlands.ClassFieldTheory.Local
