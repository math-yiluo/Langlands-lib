import Langlands.ClassFieldTheory.Local.UnitInvariants
import Langlands.Cohomology.Tate.ZeroDefinitions
import Langlands.ClassFieldTheory.Local.Norms

/-! # Degree-zero Galois Tate cohomology and the actual field norm quotient -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

section Enumeration

variable [Fintype Gal(L/K)]

/-- A base-field unit determines a class of invariant units modulo group norms. -/
def baseUnitNormClass :
    Kˣ →* Multiplicative (Langlands.Tate.InvariantsModNorm (unitsRepresentation K L)) :=
  (((Langlands.Tate.normImage (unitsRepresentation K L)).mkQ.toAddMonoidHom).comp
    (baseUnitsToInvariants K L)).toMultiplicative

/-- The coefficient norm, valued in invariants, is the embedded field norm. -/
theorem normToInvariants_units (a : Lˣ) :
    Langlands.Tate.normToInvariants (unitsRepresentation K L) (Additive.ofMul a) =
      baseUnitsToInvariants K L
        (Additive.ofMul (Langlands.LocalClassField.normUnits K L a)) := by
  apply Subtype.ext
  exact unitsRepresentation_norm K L a

/-- Vanishing of the invariant-unit class is exactly membership in the field norm image. -/
theorem baseUnitNormClass_ker :
    (baseUnitNormClass K L).ker = Langlands.LocalClassField.normSubgroup K L := by
  ext a
  change (Langlands.Tate.normImage (unitsRepresentation K L)).mkQ
      (baseUnitsToInvariants K L (Additive.ofMul a)) = 0 ↔
    a ∈ Langlands.LocalClassField.normSubgroup K L
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨Additive.toMul (b : Additive Lˣ), ?_⟩
    apply Additive.ofMul.injective
    apply baseUnitsToInvariants_injective K L
    exact (normToInvariants_units K L (Additive.toMul (b : Additive Lˣ))).symm.trans hb
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    rw [normToInvariants_units, hb]

/-- Every invariant-unit class has a representative from the base field. -/
theorem baseUnitNormClass_surjective :
    Function.Surjective (baseUnitNormClass K L) := by
  intro x
  obtain ⟨a, ha⟩ := (Langlands.Tate.normImage (unitsRepresentation K L)).mkQ_surjective
    (Multiplicative.toAdd x)
  obtain ⟨b, hb⟩ := baseUnitsToInvariants_surjective K L a
  refine ⟨Additive.toMul b, ?_⟩
  change (Langlands.Tate.normImage (unitsRepresentation K L)).mkQ
    (baseUnitsToInvariants K L b) = Multiplicative.toAdd x
  rw [hb, ha]

/-- The existing field norm quotient is the invariant-unit quotient by group norms. -/
def normQuotientEquivInvariantQuotient :
    Langlands.LocalClassField.NormQuotient K L ≃*
      Multiplicative (Langlands.Tate.InvariantsModNorm (unitsRepresentation K L)) :=
  QuotientGroup.liftEquiv _ (baseUnitNormClass_surjective K L)
    (baseUnitNormClass_ker K L).symm

@[simp] theorem normQuotientEquivInvariantQuotient_mk (a : Kˣ) :
    normQuotientEquivInvariantQuotient K L
      (Langlands.LocalClassField.normQuotientProjection K L a) =
        baseUnitNormClass K L a := rfl

end Enumeration

/-- Actual degree-zero Tate cohomology is the existing field norm quotient.
The base and extension carriers have independent universes. -/
def tateZeroEquivNormQuotient :
    relativeTateCohomology K L 0 ≃+
      Additive (Langlands.LocalClassField.NormQuotient K L) := by
  letI := Fintype.ofFinite Gal(L/K)
  exact (Langlands.Tate.zeroEquiv (unitsRepresentation K L)).toLinearEquiv.toAddEquiv.trans
    (normQuotientEquivInvariantQuotient K L).toAdditive.symm

/-- The comparison sends the Tate class of a base unit to its field norm class. -/
theorem tateZeroEquivNormQuotient_zeroClass (a : Kˣ) :
    letI := Fintype.ofFinite Gal(L/K)
    tateZeroEquivNormQuotient K L
        (Langlands.Tate.zeroClass (unitsRepresentation K L)
          (baseUnitsToInvariants K L (Additive.ofMul a))) =
      Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L a) := by
  let _ := Fintype.ofFinite Gal(L/K)
  apply (normQuotientEquivInvariantQuotient K L).toAdditive.injective
  change (normQuotientEquivInvariantQuotient K L).toAdditive
      ((normQuotientEquivInvariantQuotient K L).toAdditive.symm
        ((Langlands.Tate.zeroEquiv (unitsRepresentation K L)).hom
          (Langlands.Tate.zeroClass (unitsRepresentation K L)
            (baseUnitsToInvariants K L (Additive.ofMul a))))) = _
  erw [AddEquiv.apply_symm_apply]
  change (Langlands.Tate.zeroEquiv (unitsRepresentation K L)).toLinearEquiv
      ((Langlands.Tate.zeroEquiv (unitsRepresentation K L)).toLinearEquiv.symm
        ((Langlands.Tate.normImage (unitsRepresentation K L)).mkQ
          (baseUnitsToInvariants K L (Additive.ofMul a)))) =
    (Langlands.Tate.normImage (unitsRepresentation K L)).mkQ
      (baseUnitsToInvariants K L (Additive.ofMul a))
  exact (Langlands.Tate.zeroEquiv (unitsRepresentation K L)).toLinearEquiv.apply_symm_apply _

end Langlands.ClassFieldTheory.Local
