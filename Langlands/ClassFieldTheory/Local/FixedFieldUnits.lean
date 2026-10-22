import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Mathlib.FieldTheory.Galois.Infinite

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]

/-- The actual submodule of units fixed by a subgroup of field automorphisms. -/
abbrev fixedUnitSubmodule (H : Subgroup Gal(L/K)) :
    Submodule IntegerScalars.{u} (Additive Lˣ) :=
  Representation.invariants ((unitsRepresentation K L).ρ.comp H.subtype)

/-- Fixed units are precisely the units of the fixed field, in additive notation. -/
def fixedFieldUnitsAddEquiv (H : Subgroup Gal(L/K)) :
    fixedUnitSubmodule K L H ≃+ Additive (IntermediateField.fixedField H)ˣ where
  toFun x := Additive.ofMul <| Units.mk0
    ⟨(Additive.toMul x.1).val, by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg (fun z : Additive Lˣ => (Additive.toMul z).val) (x.2 ⟨g, hg⟩)⟩
    (by
      intro h
      exact (Additive.toMul x.1).ne_zero (congrArg Subtype.val h))
  invFun y :=
    ⟨Additive.ofMul (Units.map (IntermediateField.fixedField H).subtype.toMonoidHom
      (Additive.toMul y)), by
      intro g
      apply Units.ext
      exact (IntermediateField.mem_fixedField_iff H _).1 (Additive.toMul y).val.2 g.1 g.2⟩
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

/-- The fixed-unit identification is linear over the unchanged lifted integers. -/
def fixedFieldUnitsLinearEquiv (H : Subgroup Gal(L/K)) :
    fixedUnitSubmodule K L H ≃ₗ[IntegerScalars.{u}]
      Additive (IntermediateField.fixedField H)ˣ where
  __ := fixedFieldUnitsAddEquiv K L H
  map_smul' c x := map_zsmul (fixedFieldUnitsAddEquiv K L H) c.down x

@[simp]
theorem fixedFieldUnitsLinearEquiv_val (H : Subgroup Gal(L/K))
    (x : fixedUnitSubmodule K L H) :
    (((fixedFieldUnitsLinearEquiv K L H x).toMul : IntermediateField.fixedField H) : L) =
      (Additive.toMul x.1).val := rfl

variable [IsGalois K L]

/-- The fixed-unit identification respects the genuine quotient Galois action. -/
theorem fixedFieldUnitsLinearEquiv_intertwines (H : ClosedSubgroup Gal(L/K))
    [H.Normal] (g : Gal(L/K) ⧸ H.toSubgroup) :
    (fixedFieldUnitsLinearEquiv K L H.toSubgroup).toLinearMap ∘ₗ
        ((unitsRepresentation K L).quotientToInvariants H.toSubgroup).ρ g =
      (unitsRepresentation K (IntermediateField.fixedField H.toSubgroup)).ρ
          (InfiniteGalois.normalAutEquivQuotient H g) ∘ₗ
        (fixedFieldUnitsLinearEquiv K L H.toSubgroup).toLinearMap := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    apply LinearMap.ext
    intro x
    apply Units.ext
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes g
      (IntermediateField.fixedField H.toSubgroup)
      (fixedFieldUnitsLinearEquiv K L H.toSubgroup x).toMul.val).symm

/-- Quotient cohomology with actual fixed units is relative fixed-field cohomology. -/
def fixedFieldCohomologyIso (H : ClosedSubgroup Gal(L/K)) [H.Normal] (n : ℕ) :
    groupCohomology ((unitsRepresentation K L).quotientToInvariants H.toSubgroup) n ≅
      relativeCohomology K (IntermediateField.fixedField H.toSubgroup) n :=
  groupCohomology.mapIso (InfiniteGalois.normalAutEquivQuotient H)
    (fixedFieldUnitsLinearEquiv K L H.toSubgroup)
    (fixedFieldUnitsLinearEquiv_intertwines K L H) n

end Langlands.ClassFieldTheory.Local
