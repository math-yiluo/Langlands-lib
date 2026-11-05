import Langlands.Global.Arithmetic.AuxiliaryFirstOrderFamily
import Langlands.Global.Arithmetic.AuxiliaryFirstOrderTopology
import Langlands.HarmonicAnalysis.PadicDeepUnitNormTraceProof

/-! Construct finite-order characters with actual total-trace norm coordinates. -/

noncomputable section

namespace Langlands.Global.AuxiliaryFirstOrder

universe u v

/-- A common offset gives finite-order characters with the actual norm-pullback trace formula. -/
theorem exists_norm_coordinate_family {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier] (L : IntermediateField F.Carrier M.Carrier)
    (TF : F.TopologicalData) (TL : (intermediatePadicField F M L).TopologicalData)
    (TM : M.TopologicalData) :
    letI := TF.topology
    letI := TL.topology
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (b : Lˣ),
      ∃ C : ℕ, ∀ k : ℕ, 0 < k → ∃ χ : Lˣ →ₜ* ℂˣ,
        (∃ m : ℕ, 0 < m ∧ χ ^ m = 1) ∧
        (∀ (y : TM.Integers) (z : M.Carrierˣ),
          (z : M.Carrier) = 1 + (p : M.Carrier) ^ k * (y : M.Carrier) →
          Units.map (Algebra.norm L) z ∈ TL.principalUnits (k * TL.ramificationIndex) ∧
          χ (Units.map (Algebra.norm L) z) = Circle.toUnits
            (ψ ((p : F.Carrier) ^ ((C : ℤ) - (k : ℤ)) *
              Algebra.trace F.Carrier M.Carrier (((b : L) : M.Carrier) * (y : M.Carrier))))) := by
  let := TF.topology
  let := TL.topology
  let := TL.valuativeRel
  let := TL.localField
  let : IsScalarTower (Padic p) L M.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro ψ b
  let ψL := (TF.traceCharacter TL ψ).scale b
  obtain ⟨C, hC⟩ := exists_first_order_family (intermediatePadicField F M L) TL ψL
  refine ⟨C, fun k hk => ?_⟩
  obtain ⟨χ, hfin, hformula, hquad, hval, hlt⟩ := hC k
  let c : L := (p : L) ^ ((C : ℤ) - 2 * (k : ℤ))
  let n : ℕ := k * TL.ramificationIndex
  let a : TL.Integers := (p : TL.Integers) ^ k
  have ha : (a : L) = (p : L) ^ k := by simp [a]
  have hp : (p : L) ≠ 0 := by
    intro h
    have he := TL.ord_prime_pos
    rw [h, TL.ord_zero] at he
    omega
  have hca : c * (a : L) =
      algebraMap F.Carrier L ((p : F.Carrier) ^ ((C : ℤ) - (k : ℤ))) := by
    simp only [c, ha, map_zpow₀, map_natCast]
    rw [← zpow_natCast, ← zpow_add₀ hp]
    congr 1
    ring
  refine ⟨χ, hfin, fun y z hz => ?_⟩
  obtain ⟨z₀, hz₀, hmem, hχ⟩ := HarmonicAnalysis.padicDeepUnitNormTrace p
    (intermediatePadicField F M L) M TL TM ψL c n χ hformula a
    (by rw [ha]; exact hlt hk)
    (by rw [ha, hval]) (by simpa only [ha] using hquad) y
  have hz0z : z₀ = z := by
    apply Units.ext
    rw [hz₀, hz]
    simp only [ha, map_pow, map_natCast]
  rw [hz0z] at hmem hχ
  refine ⟨hmem, hχ.trans ?_⟩
  apply congrArg Circle.toUnits
  rw [hca]
  exact weighted_trace_character F M L TF TL ψ b _ (y : M.Carrier)

end Langlands.Global.AuxiliaryFirstOrder
