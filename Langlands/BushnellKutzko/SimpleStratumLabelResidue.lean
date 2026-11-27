import Langlands.BushnellKutzko.SimpleStratumLabelTower
import Langlands.BushnellKutzko.Labels
import Langlands.BushnellKutzko.PureStratumApproximationFieldInvariants

/-! # Residue fields and the finite fields of the label sets -/

open ValuativeRel Langlands.Henniart.Numerical

noncomputable section

namespace Langlands.BushnellKutzko.SimpleStratumLabel

universe uF uE uk

theorem natCard_polarBaseField {q : ℕ} (hq : IsPrimePow q) :
    Nat.card (polarBaseField (labelFieldSize q)) = q := by
  have hl : labelFieldSize q = q := by simp [labelFieldSize, hq.ne_one]
  have hlt : 1 < labelFieldSize q := by rw [hl]; exact hq.one_lt
  unfold polarBaseField
  rw [GaloisField.card _ _ (Nat.factorization_minFac_ne_zero hlt), hl]
  exact hq.minFac_pow_factorization_eq

/-- `𝔽_{q^D}` has `q^D` elements. -/
theorem natCard_labelField {q : ℕ} (hq : IsPrimePow q) (D : ℕ+) :
    Nat.card (polarExtensionField (labelFieldSize q) D) = q ^ (D : ℕ) := by
  unfold polarExtensionField
  rw [FiniteField.natCard_extension, natCard_polarBaseField hq]

/-- A finite field with `q^D` elements is isomorphic to the label field `𝔽_{q^D}`. -/
theorem nonempty_ringEquiv_labelField {q : ℕ} (hq : IsPrimePow q) (D : ℕ+)
    (k : Type uk) [Field k] [Finite k] (hk : Nat.card k = q ^ (D : ℕ)) :
    Nonempty (k ≃+* polarExtensionField (labelFieldSize q) D) := by
  have : Finite (polarExtensionField (labelFieldSize q) D) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_labelField hq]; exact pow_ne_zero _ hq.ne_zero)
  let := Fintype.ofFinite k
  let := Fintype.ofFinite (polarExtensionField (labelFieldSize q) D)
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hk, natCard_labelField hq]

section Residue

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

instance jacobson_isMaximal : (Ring.jacobson 𝒪[F]).IsMaximal := by
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
  infer_instance

/-- The residue ring by the Jacobson radical, as a field. -/
abbrev jacobsonResidueField : Field (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := Ideal.Quotient.field _

theorem natCard_jacobsonResidue :
    Nat.card (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) = Nat.card 𝓀[F] := by
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
  rfl

theorem finite_jacobsonResidue : Finite (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := by
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
  exact inferInstanceAs (Finite 𝓀[F])

variable (E : Type uE) [Field E] [Algebra F E] [FiniteDimensional F E]

set_option synthInstance.maxHeartbeats 400000 in
/-- The residue field of the spectral integers of `E` has `q_F^{f(E|F)}` elements. -/
theorem natCard_spectralJacobsonResidue :
    letI := LocalField.FiniteExtension.valuativeRel F E
    Nat.card (𝒪[E] ⧸ Ring.jacobson 𝒪[E]) = Nat.card 𝓀[F] ^ subfieldResidueDegree F E := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let := subfieldIntegers_isDiscreteValuationRing F E
  let O := subfieldIntegers F E
  let p : Ideal 𝒪[F] := 𝓂[F]
  let q := IsLocalRing.maximalIdeal O
  have : Algebra.IsIntegral 𝒪[F] O := inferInstanceAs
    (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  have : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  have : q.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  have : q.LiesOver p :=
    ⟨(IsLocalRing.eq_maximalIdeal (inferInstance : (q.under 𝒪[F]).IsMaximal)).symm⟩
  have hf : subfieldResidueDegree F E = Module.finrank (𝒪[F] ⧸ p) (O ⧸ q) := by
    rw [PureApproximation.subfieldResidueDegree_eq_inertiaDeg, Ideal.inertiaDeg_eq_of_isMaximal p q]
  let : Field (𝒪[F] ⧸ p) := Ideal.Quotient.field p
  have hpos : 0 < Module.finrank (𝒪[F] ⧸ p) (O ⧸ q) := by
    rw [← hf]
    have h := subfieldRamificationIndex_mul_residueDegree F E
    have : 0 < Module.finrank F E := Module.finrank_pos
    rw [← h] at this
    exact Nat.pos_of_mul_pos_left this
  have : Module.Free (𝒪[F] ⧸ p) (O ⧸ q) := Module.Free.of_divisionRing _ _
  have : Module.Finite (𝒪[F] ⧸ p) (O ⧸ q) := Module.finite_of_finrank_pos hpos
  have hcard : Nat.card (O ⧸ q) = Nat.card 𝓀[F] ^ subfieldResidueDegree F E := by
    rw [hf, Module.natCard_eq_pow_finrank (K := 𝒪[F] ⧸ p)]
    rfl
  rw [← hcard]
  let e := subfieldIntegerEquiv F E
  have hmap : Ring.jacobson 𝒪[E] = q.map e := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    have : (q.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    exact (IsLocalRing.eq_maximalIdeal this).symm
  exact Nat.card_congr (Ideal.quotientEquiv q (Ring.jacobson 𝒪[E]) e hmap).toEquiv.symm

end Residue

end Langlands.BushnellKutzko.SimpleStratumLabel
