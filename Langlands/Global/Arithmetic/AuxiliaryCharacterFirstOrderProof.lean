import Langlands.Global.Arithmetic.AuxiliaryFirstOrderCoordinates
import Langlands.Global.Arithmetic.AuxiliaryFirstOrderStabilizer
import Langlands.Global.Arithmetic.AuxiliaryFirstOrderDepth
import Langlands.Global.Arithmetic.PrimitiveTraceStabilizerProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! Assemble actual finite-order characters, arbitrary depth and exact norm stabilizers. -/

noncomputable section

namespace Langlands.Global

open AuxiliaryFirstOrder

universe u v

/-- First-order deep-unit coordinates construct the actual auxiliary characters at every prime. -/
theorem auxiliaryCharacterFirstOrder : AuxiliaryCharacterStatement.{u,v} := by
  intro p hp F M hFM hbase hfinite hGalois
  let := M.canonicalNormedField
  intro L r
  let PL := intermediatePadicField F M L
  let TF := F.canonicalTopologicalData
  let TL := PL.canonicalTopologicalData
  let TM := M.canonicalTopologicalData
  let := TF.topology
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F TF
  obtain ⟨b, hb, _, hbstab⟩ := primitiveTraceStabilizer F.Carrier M.Carrier L
  let bU : Lˣ := Units.mk0 b hb
  obtain ⟨C, hC⟩ := exists_norm_coordinate_family F M L TF TL TM ψ bU
  obtain ⟨N₁, hN₁⟩ := exists_simultaneous_trace_detection F M L TF TM b hbstab ψ
  let δ : M.Carrier →ₗ[F.Carrier] F.Carrier :=
    (Algebra.trace F.Carrier M.Carrier).comp (LinearMap.mul F.Carrier M.Carrier (b : M.Carrier))
  obtain ⟨N₂, hN₂⟩ := exists_simultaneous_linear_detection F M TF TM
    (fun _ : Unit => δ) (fun _ => weighted_trace_ne_zero L b hb) ψ
  let k : ℕ := C + N₁ + N₂ + r + 1
  let N : ℕ := k - C
  have hk : 0 < k := by omega
  have hkr : r < k := by omega
  have hN₁le : N₁ ≤ N := by omega
  have hN₂le : N₂ ≤ N := by omega
  have hexp : (C : ℤ) - (k : ℤ) = -(N : ℤ) := by omega
  obtain ⟨χ, hfin, hcoords⟩ := hC k hk
  have htop : TL.topology = (inferInstance : TopologicalSpace L) :=
    intermediate_topology_eq F M L TL
  let χ' : Lˣ →ₜ* ℂˣ := transportUnitCharacter TL.topology _ htop χ
  have hχ' (x : Lˣ) : χ' x = χ x := transportUnitCharacter_apply _ _ htop χ x
  have hfin' : ∃ m : ℕ, 0 < m ∧ χ' ^ m = 1 := by
    obtain ⟨m, hm, hχm⟩ := hfin
    refine ⟨m, hm, ContinuousMonoidHom.ext fun x => ?_⟩
    simp only [ContinuousMonoidHom.pow_apply]
    rw [hχ']
    change χ x ^ m = 1
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] using
      congrArg (fun τ => τ x) hχm
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hsmall : ‖algebraMap F.Carrier M.Carrier ((p : F.Carrier) ^ k)‖ < 1 := by
    simp only [map_pow, map_natCast]
    change M.canonicalNorm ((p : M.Carrier) ^ k) < 1
    rw [canonicalNorm_prime_pow]
    simpa only [zpow_zero] using zpow_lt_zpow_right₀ hp1 (show -(k : ℤ) < 0 by omega)
  have hstab : HasExactUnitNormStabilizer L χ'.toMonoidHom := by
    apply exact_stabilizer_of_integral_coordinates F M L TF ψ b
      ((p : F.Carrier) ^ k) ((p : F.Carrier) ^ ((C : ℤ) - (k : ℤ)))
      χ'.toMonoidHom hsmall
    · intro y z hz
      have hz' : (z : M.Carrier) = 1 + (p : M.Carrier) ^ k * (y : M.Carrier) := by
        simpa only [map_pow, map_natCast] using hz
      change χ' (Units.map (Algebra.norm L) z) = _
      rw [hχ']
      exact (hcoords y z hz').2
    · intro σ hσ
      obtain ⟨y, hy⟩ := hN₁ N hN₁le σ hσ
      exact ⟨y, by simpa only [hexp] using hy⟩
  obtain ⟨y, hy⟩ := hN₂ N hN₂le ()
  change ψ.complex ((p : F.Carrier) ^ (-(N : ℤ)) *
    Algebra.trace F.Carrier M.Carrier ((b : M.Carrier) * (y : M.Carrier))) ≠ 1 at hy
  obtain ⟨z, hz, _⟩ := exists_norm_one_coordinate_unit M k hk y
  obtain ⟨hmem, hvalue⟩ := hcoords y z hz
  let x : Lˣ := Units.map (Algebra.norm L) z
  have hxχ : χ' x ≠ 1 := by
    intro h
    rw [hχ'] at h
    apply hy
    have hv : Circle.toUnits (ψ ((p : F.Carrier) ^ (-(N : ℤ)) *
        Algebra.trace F.Carrier M.Carrier ((b : M.Carrier) * (y : M.Carrier)))) = 1 := by
      rw [← hexp]
      exact hvalue.symm.trans h
    exact congrArg (fun a : ℂˣ => (a : ℂ)) hv
  have hpL : (p : L) ≠ 0 := by
    let : CharZero L := Algebra.charZero_of_charZero (Padic p) L
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hprimeval : TL.discreteValuation ((p : L) ^ k) =
      WithZero.exp (-((k * TL.ramificationIndex : ℕ) : ℤ)) := by
    rw [← zpow_natCast, valuation_prime_zpow]
    simp only [Nat.cast_mul, TL.ramificationIndex_cast]
    congr 1
    ring
  have hle : TL.discreteValuation ((x : L) - 1) ≤ TL.discreteValuation ((p : L) ^ k) := by
    rw [hprimeval]
    exact hmem.2
  have hdepth : ‖((x : L) : M.Carrier) - 1‖ < (p : ℝ) ^ (-(r : ℤ)) := by
    change M.canonicalNorm (((x : L) - 1 : L) : M.Carrier) < _
    rw [← intermediate_canonicalNorm_eq F M L ((x : L) - 1)]
    calc
      PL.canonicalNorm ((x : L) - 1) ≤ PL.canonicalNorm ((p : L) ^ k) :=
        canonicalNorm_le_of_valuation_le TL _ _ (pow_ne_zero k hpL) hle
      _ = (p : ℝ) ^ (-(k : ℤ)) := canonicalNorm_prime_pow PL k
      _ < (p : ℝ) ^ (-(r : ℤ)) := zpow_lt_zpow_right₀ hp1 (by omega)
  exact ⟨χ', hfin', ⟨x, hdepth, hxχ⟩, hstab⟩

end Langlands.Global
