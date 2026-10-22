import Langlands.ClassFieldTheory.Local.FixedFieldUnits
import Langlands.ClassFieldTheory.Local.ClosureCoefficients

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K]

/-- The actual discrete module of algebraic-closure units with its continuous action. -/
def absoluteUnitDiscreteModule :
    DiscreteModule IntegerScalars.{u} (Field.absoluteGaloisGroup K) where
  toTopRep := absoluteUnits K
  isDiscrete := inferInstance
  continuous_action := continuous_unitAction K (AlgebraicClosure K)

@[simp]
theorem absoluteUnitDiscreteModule_toTopRep :
    (absoluteUnitDiscreteModule K).toTopRep = absoluteUnits K := rfl

variable [CharZero K]

/-- The actual field fixed by an open normal subgroup of the absolute Galois group. -/
abbrev finiteStageFixedField (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField N.toSubgroup

/-- An open normal subgroup, viewed as a closed subgroup without changing its carrier. -/
def finiteStageClosedSubgroup (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    ClosedSubgroup Gal(AlgebraicClosure K/K) :=
  ⟨N.toSubgroup, N.toOpenSubgroup.isClosed⟩

instance finiteStageClosedSubgroup_normal
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    (finiteStageClosedSubgroup K N).Normal := N.isNormal'

instance finiteStageFixedField_finiteDimensional
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    FiniteDimensional K (finiteStageFixedField K N) := by
  apply (InfiniteGalois.isOpen_iff_finite (finiteStageFixedField K N)).mp
  change IsOpen
    (IntermediateField.fixedField (finiteStageClosedSubgroup K N).toSubgroup).fixingSubgroup.carrier
  rw [InfiniteGalois.fixingSubgroup_fixedField]
  exact N.toOpenSubgroup.isOpen

instance finiteStageFixedField_isGalois
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IsGalois K (finiteStageFixedField K N) := by
  exact @IsGalois.of_fixedField_normal_subgroup K (AlgebraicClosure K) _ _ _
    inferInstance N.toSubgroup N.isNormal'

/-- Cohomology of the actual fixed-unit stage, identified with relative cohomology. -/
def finiteStageRelativeIso (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) (q : ℕ) :
    groupCohomology (finiteQuotientRep (absoluteUnitDiscreteModule K).toRep N) q ≅
      relativeCohomology K (finiteStageFixedField K N) q :=
  fixedFieldCohomologyIso K (AlgebraicClosure K) (finiteStageClosedSubgroup K N) q

variable (E : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K E] [IsGalois K E]

/-- The actual fixing subgroup of a finite Galois intermediate field, bundled as open normal. -/
def finiteGaloisFixingSubgroup : OpenNormalSubgroup (Field.absoluteGaloisGroup K) where
  toSubgroup := E.fixingSubgroup
  isOpen' := IntermediateField.fixingSubgroup_isOpen E
  isNormal' := IsGalois.fixingSubgroup_normal_of_isGalois E

@[simp]
theorem finiteGaloisFixingSubgroup_toSubgroup :
    (finiteGaloisFixingSubgroup K E).toSubgroup = E.fixingSubgroup := rfl

@[simp]
theorem finiteStageFixedField_finiteGaloisFixingSubgroup :
    finiteStageFixedField K (finiteGaloisFixingSubgroup K E) = E :=
  InfiniteGalois.fixedField_fixingSubgroup E

/-- The quotient equivalence induced by restriction of closure automorphisms to `E`. -/
def finiteGaloisStageGroupEquiv :
    Field.absoluteGaloisGroup K ⧸ (finiteGaloisFixingSubgroup K E).toSubgroup ≃* Gal(E/K) :=
  QuotientGroup.liftEquiv (finiteGaloisFixingSubgroup K E).toSubgroup
    (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K))
    E.restrictNormalHom_ker.symm

@[simp]
theorem finiteGaloisStageGroupEquiv_mk (σ : Field.absoluteGaloisGroup K) :
    finiteGaloisStageGroupEquiv K E (QuotientGroup.mk σ) = closureRestriction K E σ := rfl

@[simp]
theorem finiteGaloisStageGroupEquiv_symm_restriction (σ : Field.absoluteGaloisGroup K) :
    (finiteGaloisStageGroupEquiv K E).symm (closureRestriction K E σ) =
      QuotientGroup.mk σ :=
  (finiteGaloisStageGroupEquiv K E).symm_apply_apply (QuotientGroup.mk σ)

/-- The actual fixed units are units of `E`, with inverse the inclusion into the closure. -/
def finiteGaloisStageUnitsAddEquiv :
    fixedUnitSubmodule K (AlgebraicClosure K) E.fixingSubgroup ≃+ Additive Eˣ where
  toFun x := Additive.ofMul <| Units.mk0
    ⟨(Additive.toMul x.1).val, by
      have hx := (fixedFieldUnitsLinearEquiv K (AlgebraicClosure K)
        E.fixingSubgroup x).toMul.val.2
      change (Additive.toMul x.1).val ∈ IntermediateField.fixedField E.fixingSubgroup at hx
      exact (congrArg (fun F : IntermediateField K (AlgebraicClosure K) =>
        (Additive.toMul x.1).val ∈ F) (InfiniteGalois.fixedField_fixingSubgroup E)).mp hx⟩
    (by
      intro h
      exact (Additive.toMul x.1).ne_zero (congrArg Subtype.val h))
  invFun y :=
    ⟨Additive.ofMul (Units.map E.subtype.toMonoidHom (Additive.toMul y)), by
      intro g
      apply Units.ext
      exact (IntermediateField.mem_fixingSubgroup_iff E g.1).1 g.2
        (Additive.toMul y).val (Additive.toMul y).val.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv y := by
    apply Units.ext
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Units.ext
    apply Subtype.ext
    rfl

/-- The same equivalence, linear over the unchanged lifted integer scalars. -/
def finiteGaloisStageUnitsLinearEquiv :
    finiteQuotientRep (absoluteUnitDiscreteModule K).toRep (finiteGaloisFixingSubgroup K E)
      ≃ₗ[IntegerScalars.{u}] Additive Eˣ where
  __ := finiteGaloisStageUnitsAddEquiv K E
  map_smul' c x := map_zsmul (finiteGaloisStageUnitsAddEquiv K E) c.down x

@[simp]
theorem finiteGaloisStageUnitsLinearEquiv_val
    (x : finiteQuotientRep (absoluteUnitDiscreteModule K).toRep
      (finiteGaloisFixingSubgroup K E)) :
    (((finiteGaloisStageUnitsLinearEquiv K E x).toMul : E) : AlgebraicClosure K) =
      (Additive.toMul x.1).val := rfl

@[simp]
theorem finiteGaloisStageUnitsLinearEquiv_symm_val (y : Additive Eˣ) :
    ((finiteGaloisStageUnitsLinearEquiv K E).symm y).val =
      unitInclusionLinear E (AlgebraicClosure K) y := rfl

@[simp]
theorem finiteGaloisStageUnitsLinearEquiv_inclusion
    (x : finiteQuotientRep (absoluteUnitDiscreteModule K).toRep
      (finiteGaloisFixingSubgroup K E)) :
    unitInclusionLinear E (AlgebraicClosure K) (finiteGaloisStageUnitsLinearEquiv K E x) =
      x.val := by
  apply Units.ext
  rfl

/-- Equivariance for the genuine quotient action and the restriction group equivalence. -/
theorem finiteGaloisStageUnitsLinearEquiv_intertwines
    (g : Field.absoluteGaloisGroup K ⧸ (finiteGaloisFixingSubgroup K E).toSubgroup) :
    (finiteGaloisStageUnitsLinearEquiv K E).toLinearMap ∘ₗ
        (finiteQuotientRep (absoluteUnitDiscreteModule K).toRep
          (finiteGaloisFixingSubgroup K E)).ρ g =
      (unitsRepresentation K E).ρ (finiteGaloisStageGroupEquiv K E g) ∘ₗ
        (finiteGaloisStageUnitsLinearEquiv K E).toLinearMap := by
  induction g using QuotientGroup.induction_on with
  | H σ =>
    apply LinearMap.ext
    intro x
    apply Units.ext
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ E
      (finiteGaloisStageUnitsLinearEquiv K E x).toMul.val).symm

/-- Direct identification with relative cohomology of the specified finite Galois field. -/
def finiteGaloisStageRelativeIso (q : ℕ) :
    groupCohomology (finiteQuotientRep (absoluteUnitDiscreteModule K).toRep
      (finiteGaloisFixingSubgroup K E)) q ≅ relativeCohomology K E q :=
  groupCohomology.mapIso (finiteGaloisStageGroupEquiv K E)
    (finiteGaloisStageUnitsLinearEquiv K E)
    (finiteGaloisStageUnitsLinearEquiv_intertwines K E) q

end Langlands.ClassFieldTheory.Local
