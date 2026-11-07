import Langlands.LocalFactor.RankOneStationaryPhase
import Langlands.LocalFactor.RankOneStabilityCoset

noncomputable section

open MeasureTheory

namespace Langlands.LocalFactor

universe u

/-- Rank-one stability for every supplied topology and every supplied Haar measure. -/
theorem rankOneStability : RankOneStabilityStatement.{u} := by
  intro p hp F T
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  intro χ ψ ha
  refine ⟨RankOneStability.conductor_and_L T χ ha, ?_⟩
  let a := T.multiplicativeConductor χ
  let k := a / 2
  let m := a - k
  have ha' : 2 ≤ a := ha
  have hm : 0 < m := by dsimp [m, k]; omega
  have hma : m < a := by dsimp [m, k]; omega
  have hquad : a ≤ 2 * m := by dsimp [m, k]; omega
  have hlevels : a = m + k := by dsimp [m, k]; omega
  have hkm : k ≤ m := by dsimp [m, k]; omega
  obtain ⟨c, hc0, hc, hlin⟩ :=
    RankOneStability.exists_deep_linearization T χ ψ hm hma hquad
  let d := Units.mk0 c hc0
  have hd : T.ord (d : F.Carrier) = -(T.additiveConductor ψ + a) := by
    change T.ord c = _
    rw [hc]
    dsimp [a]
    omega
  have hγ : RankOneTwistWitness T χ ψ d⁻¹ := by
    intro η hη μ s
    have hηk : T.multiplicativeConductor η ≤ k := by dsimp [k, a]; omega
    have hηm : T.multiplicativeConductor η ≤ m := hηk.trans hkm
    have hcond := (RankOneStability.conductor_and_L T χ ha η hη).1
    have hint := RankOneStability.gauss_integral_twist T χ η ψ μ a m k hm
      hlevels hηk hηm d hd hlin
    have ha0 : a ≠ 0 := by omega
    have heps0 :
        PadicAbelian.epsilonAt T (PadicAbelian.uniformizerUnit T) (χ * η)
          ψ.toAddChar μ.measure a (T.additiveConductor ψ) 0 =
        (η d⁻¹ : ℂ) *
          PadicAbelian.epsilonAt T (PadicAbelian.uniformizerUnit T) χ
            ψ.toAddChar μ.measure a (T.additiveConductor ψ) 0 := by
      simpa only [PadicAbelian.epsilonAt, ite_eq_right ha0] using hint
    dsimp only [PadicAbelian.epsilon]
    rw [hcond]
    change PadicAbelian.epsilonAt T (PadicAbelian.uniformizerUnit T) (χ * η)
        ψ.toAddChar μ.measure a (T.additiveConductor ψ) s =
      (η d⁻¹ : ℂ) * PadicAbelian.epsilonAt T (PadicAbelian.uniformizerUnit T) χ
        ψ.toAddChar μ.measure a (T.additiveConductor ψ) s
    rw [PadicAbelian.epsilonAt_eq_zero_mul T _ (χ * η),
      PadicAbelian.epsilonAt_eq_zero_mul T _ χ, heps0, mul_assoc]
  refine ⟨d⁻¹, ?_, hγ, ?_⟩
  · rw [Units.val_inv_eq_inv_val, T.ord_inv, hd]
    dsimp [a]
    omega
  · exact PadicAbelian.rankOneTwistWitness_iff_mem_coset T χ ψ d⁻¹ hγ

end Langlands.LocalFactor
