import Langlands.Global.Arithmetic.AuxiliaryFirstOrderHelpers
import Langlands.Global.Arithmetic.AuxiliaryCharacterStatement

/-! Exact actual unit-norm stabilizers from computed first-order trace coordinates. -/

noncomputable section

namespace Langlands.Global.AuxiliaryFirstOrder

universe u v

/-- Integral first-order trace coordinates and detection imply the exact norm stabilizer. -/
theorem exact_stabilizer_of_integral_coordinates {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier]
    (L : IntermediateField F.Carrier M.Carrier) (TF : F.TopologicalData) :
    letI := M.canonicalNormedField
    letI := TF.topology
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (b : L)
      (a t : F.Carrier) (χ : Lˣ →* ℂˣ),
      ‖algebraMap F.Carrier M.Carrier a‖ < 1 →
      (∀ y : M.canonicalTopologicalData.Integers, ∀ z : M.Carrierˣ,
        (z : M.Carrier) = 1 + algebraMap F.Carrier M.Carrier a * (y : M.Carrier) →
        χ (Units.map (Algebra.norm L) z) =
          Circle.toUnits (ψ (t * Algebra.trace F.Carrier M.Carrier
            ((b : M.Carrier) * (y : M.Carrier))))) →
      (∀ σ : M.Carrier ≃ₐ[F.Carrier] M.Carrier, σ ∉ L.fixingSubgroup →
        ∃ y : M.canonicalTopologicalData.Integers,
          ψ.complex (t * traceDifference L b σ (y : M.Carrier)) ≠ 1) →
      HasExactUnitNormStabilizer L χ := by
  let := M.canonicalNormedField
  let := TF.topology
  intro ψ b a t χ ha hcoords hdetect
  have hna : IsNonarchimedean (norm : M.Carrier → ℝ) :=
    isNonarchimedean_spectralNorm (K := Padic p) (L := M.Carrier)
  intro σ
  constructor
  · intro hstab
    by_contra hσ
    obtain ⟨y, hy⟩ := hdetect σ hσ
    have hynorm : ‖(y : M.Carrier)‖ ≤ 1 :=
      (M.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers _).mpr y.property
    have hsmall : ‖algebraMap F.Carrier M.Carrier a * (y : M.Carrier)‖ < 1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hynorm (norm_nonneg _)).trans_lt (by simpa using ha)
    have hnorm : ‖1 + algebraMap F.Carrier M.Carrier a * (y : M.Carrier)‖ = 1 := by
      simpa only [norm_one] using hna.add_eq_left_of_lt
        (a := algebraMap F.Carrier M.Carrier a * (y : M.Carrier)) (b := (1 : M.Carrier))
        norm_neg (by simpa only [norm_one] using hsmall)
    have hz0 : 1 + algebraMap F.Carrier M.Carrier a * (y : M.Carrier) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact zero_ne_one hnorm
    let z : M.Carrierˣ := Units.mk0 _ hz0
    have hyσ : σ (y : M.Carrier) ∈ M.canonicalTopologicalData.Integers := by
      rw [← M.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers]
      have he : M.canonicalNorm (σ (y : M.Carrier)) = M.canonicalNorm (y : M.Carrier) := by
        simpa using Weil.Local.canonicalNorm_map M M
          (σ.restrictScalars (Padic p)).toAlgHom (y : M.Carrier)
      exact he.le.trans hynorm
    let yσ : M.canonicalTopologicalData.Integers := ⟨σ (y : M.Carrier), hyσ⟩
    have hσz : ((Units.map σ.toRingEquiv.toMonoidHom z : M.Carrierˣ) : M.Carrier) =
        1 + algebraMap F.Carrier M.Carrier a * (yσ : M.Carrier) := by
      change σ (1 + algebraMap F.Carrier M.Carrier a * (y : M.Carrier)) = _
      rw [map_add, map_one, map_mul, σ.commutes]
    have heq : Circle.toUnits (ψ (t * Algebra.trace F.Carrier M.Carrier
        ((b : M.Carrier) * σ (y : M.Carrier)))) =
        Circle.toUnits (ψ (t * Algebra.trace F.Carrier M.Carrier
          ((b : M.Carrier) * (y : M.Carrier)))) := by
      calc
        _ = χ (Units.map (Algebra.norm L) (Units.map σ.toRingEquiv.toMonoidHom z)) :=
          (hcoords yσ _ hσz).symm
        _ = χ (Units.map (Algebra.norm L) z) := hstab z hnorm
        _ = _ := hcoords y z rfl
    have heqc : ψ.complex (t * Algebra.trace F.Carrier M.Carrier
        ((b : M.Carrier) * σ (y : M.Carrier))) =
        ψ.complex (t * Algebra.trace F.Carrier M.Carrier
          ((b : M.Carrier) * (y : M.Carrier))) :=
      congrArg (fun w : ℂˣ => (w : ℂ)) heq
    apply hy
    rw [traceDifference_apply, mul_sub, AddChar.map_sub_eq_div, heqc]
    exact div_self (ψ _).coe_ne_zero
  · intro hσ z hz
    exact congrArg χ (norm_units_fixed L σ hσ z)

end Langlands.Global.AuxiliaryFirstOrder
