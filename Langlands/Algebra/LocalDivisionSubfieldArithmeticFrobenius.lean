import Langlands.Algebra.LocalDivisionReducedDegree
import Langlands.Algebra.CyclicFieldNormCommutator
import Mathlib.FieldTheory.Finite.Basic

/-! # Arithmetic Frobenius of a full-residue division subfield -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel
open scoped WithZero

universe u s

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local notation "kD" => DivisionValuation.Residue (localReducedNormValuation K D)

local instance divisionArithmeticResidueField : Field kD := localDivisionResidueField K D
local instance divisionArithmeticResidueAlgebra : Algebra 𝓀[K] kD := localDivisionResidueAlgebra K D

section Embedded

variable {L : Type s} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (ι : L →ₐ[K] D)
  (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
  (hdeg : Module.finrank K L = CentralSimple.reducedDegree K D)
  (hinj : Function.Injective (localDivisionSubfieldGaloisReduction K D ι hsurj))

/-- A faithful reduction on a full-residue Galois subfield of reduced degree
identifies its Galois group with the entire residue Galois group. -/
def localDivisionSubfieldResidueGaloisEquiv : (L ≃ₐ[K] L) ≃* (kD ≃ₐ[𝓀[K]] kD) :=
  MulEquiv.ofBijective (localDivisionSubfieldGaloisReduction K D ι hsurj)
    (hinj.bijective_of_nat_card_le (by
      let : IsGalois 𝓀[K] kD := inferInstance
      rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, hdeg,
        localDivisionResidue_finrank_eq_reducedDegree]))

/-- Lift the base residue cardinality power to the original full-residue subfield. -/
def localDivisionSubfieldArithmeticFrobenius : L ≃ₐ[K] L :=
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  (localDivisionSubfieldResidueGaloisEquiv K D ι hsurj hdeg hinj).symm
    (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] kD)

/-- Its action is the arithmetic power on the actual division-algebra residue. -/
theorem localDivisionSubfieldArithmeticFrobenius_residue (x : kD) :
    localDivisionSubfieldGaloisReduction K D ι hsurj
      (localDivisionSubfieldArithmeticFrobenius K D ι hsurj hdeg hinj) x = x ^ Nat.card 𝓀[K] := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  let e := localDivisionSubfieldResidueGaloisEquiv K D ι hsurj hdeg hinj
  change e (e.symm (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] kD)) x = _
  rw [e.apply_symm_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card]

/-- The arithmetic automorphism has exact order equal to the reduced degree. -/
theorem localDivisionSubfieldArithmeticFrobenius_orderOf :
    orderOf (localDivisionSubfieldArithmeticFrobenius K D ι hsurj hdeg hinj) =
      CentralSimple.reducedDegree K D := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  let e := (localDivisionSubfieldResidueGaloisEquiv K D ι hsurj hdeg hinj).symm
  let f := FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] kD
  change orderOf (e f) = _
  exact (orderOf_injective e.toMonoidHom e.injective f).trans
    ((FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic 𝓀[K] kD).trans
      (localDivisionResidue_finrank_eq_reducedDegree K D))

/-- The arithmetic power formula on integral elements, expressed by their
strict difference valuation in the same division algebra. -/
theorem localDivisionSubfieldArithmeticFrobenius_sub_lt_one
    (a : (localDivisionSubfieldValuation K D ι).integer) :
    localReducedNormIntValuation K D
      (ι (localDivisionSubfieldArithmeticFrobenius K D ι hsurj hdeg hinj a.val) -
        ι (a.val ^ Nat.card 𝓀[K])) < 1 := by
  let σ := localDivisionSubfieldArithmeticFrobenius K D ι hsurj hdeg hinj
  let B := localDivisionSubfieldIntegerMap K D ι
  let r := DivisionValuation.reduction (localReducedNormValuation K D)
  have h := localDivisionSubfieldArithmeticFrobenius_residue K D ι hsurj hdeg hinj (r (B a))
  change localDivisionSubfieldFullResidueAut K D ι hsurj σ
    (localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ a)) = _ at h
  rw [localDivisionSubfieldFullResidueAut_reduction] at h
  change r (B (localDivisionSubfieldIntegerAut K D ι σ a)) = (r (B a)) ^ _ at h
  rw [← map_pow, ← map_pow] at h
  have hval := (DivisionValuation.reduction_eq_iff _ _ _).mp h
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (localReducedNormValuation K D _) < 1
  rw [← map_one e]
  exact e.toOrderIso.lt_iff_lt.mpr hval

end Embedded

/-- A full-residue degree-d subfield admits the arithmetic lift and a division
unit implementing it by conjugation. The central power normalization is a
separate condition on the implementing unit. -/
theorem exists_localDivision_fullResidue_arithmeticFrobenius :
    ∃ b : (localReducedNormValuation K D).integer,
      letI := residueGeneratorField K D (b : D)
      let E := residueGeneratorSubalgebra K D (b : D)
      Function.Surjective (localDivisionSubfieldResidueMap K D E.val) ∧
        Module.finrank K E = CentralSimple.reducedDegree K D ∧ IsGalois K E ∧
        ∃ σ : E ≃ₐ[K] E, orderOf σ = CentralSimple.reducedDegree K D ∧
          (∀ a : (localDivisionSubfieldValuation K D E.val).integer,
            localReducedNormIntValuation K D
              (E.val (σ (a : E)) - E.val ((a : E) ^ Nat.card 𝓀[K])) < 1) ∧
          ∃ j : Dˣ, ∀ a : E, (j : D) * E.val a = E.val (σ a) * (j : D) := by
  obtain ⟨f, b, hmon, hres, hmin, hsep, hsurj, hdim⟩ :=
    exists_localDivision_fullResidue_polynomial_subfield K D
  let := residueGeneratorField K D (b : D)
  let E := residueGeneratorSubalgebra K D (b : D)
  have hsepR : (f.map (IsLocalRing.residue 𝒪[K])).Separable := by
    rw [hres]
    exact PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
  have hsplitR : ((f.map (IsLocalRing.residue 𝒪[K])).map (algebraMap 𝓀[K] kD)).Splits := by
    let : IsGalois 𝓀[K] kD := inferInstance
    rw [hres]
    exact IsGalois.splits 𝓀[K] _
  have hsplit : ((minpoly K (b : D)).map (algebraMap K E)).Splits := by
    rw [← hmin]
    exact localDivisionSubfield_splits_base_polynomial K D E.val hsurj f hmon hsepR hsplitR
  let : Polynomial.IsSplittingField K E (minpoly K (b : D)) :=
    residueGenerator_isSplittingField K D (b : D) hsplit
  let : IsGalois K E := IsGalois.of_separable_splitting_field hsep
  let a : (localDivisionSubfieldValuation K D E.val).integer :=
    ⟨⟨(b : D), residueGenerator_mem K D (b : D)⟩, b.prop⟩
  have hroot : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D E.val) a = 0 := by
    let θ : (localDivisionSubfieldValuation K D E.val).integer →+* D :=
      E.val.toRingHom.comp (localDivisionSubfieldValuation K D E.val).integer.subtype
    have hθ : θ.comp (localDivisionSubfieldBaseIntegerMap K D E.val) =
        (algebraMap K D).comp (algebraMap 𝒪[K] K) := by
      ext c
      exact E.val.commutes c.val
    apply (E.val.injective.comp Subtype.val_injective)
    change θ (f.eval₂ (localDivisionSubfieldBaseIntegerMap K D E.val) a) = θ 0
    rw [map_zero, Polynomial.hom_eval₂, hθ, ← Polynomial.eval₂_map]
    change Polynomial.aeval (b : D) (f.map (algebraMap 𝒪[K] K)) = 0
    rw [hmin]
    exact minpoly.aeval K (b : D)
  have hinj := localDivisionSubfieldGaloisReduction_injective K D E.val hsurj
    (residueGeneratorPowerBasis K D (b : D)) a rfl f hroot hsepR
  have hdeg := hdim.trans (localDivisionResidue_finrank_eq_reducedDegree K D)
  let σ := localDivisionSubfieldArithmeticFrobenius K D E.val hsurj hdeg hinj
  let j := implementingUnit E.val σ
  refine ⟨b, hsurj, hdeg, inferInstanceAs (IsGalois K E), σ,
    localDivisionSubfieldArithmeticFrobenius_orderOf K D E.val hsurj hdeg hinj,
    localDivisionSubfieldArithmeticFrobenius_sub_lt_one K D E.val hsurj hdeg hinj, j, ?_⟩
  intro x
  change (j : D) * E.val x = E.val (σ x) * (j : D)
  rw [← implementingUnit_conj E.val σ x]
  simp [j, mul_assoc]

end Langlands.CentralDivision
