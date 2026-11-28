import Langlands.BaseChange.CentralQuotientFormalDegree
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceOrthogonality
import Langlands.Representation.Smooth.Contragredient.Equivalence

/-! # The trace of a square-integrable representation on a conjugate coefficient -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory JacquetLanglands HarishChandraSchwartz

universe u uV uW

section Schur

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

open Classical in
/-- **Schur orthogonality for the trace on a conjugate coefficient.** Let `ρ` and `π` be
irreducible representations of `GL_n(F)`, square integrable modulo the center `Z`, with the
same unitary central character, and `d` the formal degree of `π` for the Haar measure `μ` on
`G / Z`. For a compact open subgroup `H` fixing `v` and a smooth functional `ℓ` of `π`, the
function `gZ ↦ ψ^ρ_H(g) conj ℓ(π(g) v)`, with `ψ^ρ_H(g) = trace(e_H ρ(g) e_H)` the trace
coefficient of `ρ`, is well defined and integrable on `G / Z`, and its integral is
`d⁻¹ conj ℓ(v)` if `ρ ≅ π` and `0` otherwise. -/
theorem exists_integral_traceCoefficient_mul_star_coefficient :
    letI := centralQuotientMeasurableSpace F n
    ∀ (μ : Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)))
      [μ.IsHaarMeasure] (ρ : Representation ℂ (GeneralLinear n F) V)
      (π : Representation ℂ (GeneralLinear n F) W)
      (hρ : IsSquareIntegrable ρ), IsSquareIntegrable π → ρ.IsIrreducible → π.IsIrreducible →
      ∀ (cρ : UnitaryCentralCharacter ρ) (cπ : UnitaryCentralCharacter π),
        cρ.character = cπ.character →
        ∀ d : ℝ, IsCentralFormalDegree μ π d →
        ∀ (H : CompactOpenSubgroup (GeneralLinear n F)) (v : W),
          v ∈ fixedVectors π H.toSubgroup → ∀ ℓ : SmoothDual π,
          ∃ T : GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F) → ℂ,
            (∀ g : GeneralLinear n F, T (QuotientGroup.mk g) =
              traceCoefficient ρ hρ.isAdmissible.1 H g * star (ℓ.val (π g v))) ∧
            Integrable T μ ∧
            (∫ q, T q ∂μ) =
              if Nonempty (ρ.Equiv π) then (d : ℂ)⁻¹ * star (ℓ.val v) else 0 := by
  classical
  intro μ _ ρ π hρ hπ hiρ hiπ cρ cπ hc d hd H v hv ℓ
  let G := GeneralLinear n F
  let Z := Subgroup.center G
  let : MeasurableSpace (G ⧸ Z) := centralQuotientMeasurableSpace F n
  have : BorelSpace (G ⧸ Z) := centralQuotientBorelSpace F n
  have : μ.IsInvInvariant := centralQuotient_isInvInvariant F n μ
  have hcof := LevelZero.compactOpen_cofinal (F := F) n
  let χ := cπ.character
  have hρχ : ∀ (a : Z) (x : V), ρ a x = (χ a : ℂ) • x := fun a x => by
    rw [cρ.acts, hc]
  have hπχ : ∀ (a : Z) (x : W), π a x = (χ a : ℂ) • x := cπ.acts
  have hsqρ := (isSquareIntegrableModCentralSubgroup_center_iff ρ μ).mpr (hρ μ)
  have hsqπ := (isSquareIntegrableModCentralSubgroup_center_iff π μ).mpr (hπ μ)
  have hρa : IsAdmissible ρ := hρ.isAdmissible
  have hπa : IsAdmissible π := hπ.isAdmissible
  obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrable Z le_rfl μ hπχ hcof hsqπ hiπ
  obtain ⟨w, hw⟩ := b.toSmoothDual_surjective hcof hπa ℓ
  let ℓv : SmoothDual π := b.toSmoothDual hπa.1 v
  have : FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup) := hρa.2 H.1
  let β := Module.finBasis ℂ (fixedVectors ρ H.toSubgroup)
  let ℓi : Fin (Module.finrank ℂ (fixedVectors ρ H.toSubgroup)) → SmoothDual ρ :=
    fun i => fixedFunctional ρ hρa.1 H (β.coord i)
  let f : Fin (Module.finrank ℂ (fixedVectors ρ H.toSubgroup)) → G ⧸ Z → ℂ :=
    fun i => orthogonalityIntegrand Z hρχ hπχ ((β i : fixedVectors ρ H.toSubgroup) : V)
      (ℓi i).val w ℓv.val
  have hstar : ∀ g : G, star (ℓ.val (π g v)) = ℓv.val (π g⁻¹ w) := by
    intro g
    rw [← hw]
    change star (b.inner w (π g v)) = b.inner v (π g⁻¹ w)
    rw [← b.invariant g v (π g⁻¹ w), Representation.self_inv_apply]
    exact b.conj_inner_symm (π g v) w
  have hfint : ∀ i, Integrable (f i) μ := fun i =>
    integrable_orthogonalityIntegrand Z le_rfl μ hρχ hπχ hsqρ hsqπ _ (ℓi i) w ℓv
  refine ⟨fun q => ∑ i, f i q, ?_, integrable_finsetSum _ fun i _ => hfint i, ?_⟩
  · intro g
    rw [hstar g, traceCoefficient_eq_sum ρ hρa.1 H β g, Finset.sum_mul]
    rfl
  rw [integral_finsetSum _ fun i _ => hfint i]
  by_cases hne : Nonempty (ρ.Equiv π)
  · obtain ⟨e⟩ := hne
    rw [ite_eq_left (⟨e⟩ : Nonempty (ρ.Equiv π))]
    -- The `i`-th Schur integral, by the formal degree of `π` after transport along `e`.
    have hterm : ∀ i, ∫ q, f i q ∂μ =
        (d : ℂ)⁻¹ * ℓv.val (e ((β i : fixedVectors ρ H.toSubgroup) : V)) *
          (ℓi i).val (e.symm w) := by
      intro i
      let ℓ' : SmoothDual π := smoothContragredientEquiv e.symm (ℓi i)
      obtain ⟨s, hs, -, hsint⟩ :=
        hd.2 (e ((β i : fixedVectors ρ H.toSubgroup) : V)) w ℓ' ℓv
      have hfs : f i = s := by
        funext q
        induction q using QuotientGroup.induction_on with
        | H g =>
          rw [hs g]
          change (ℓi i).val (ρ g ((β i : fixedVectors ρ H.toSubgroup) : V)) *
              ℓv.val (π g⁻¹ w) =
            (ℓi i).val (e.symm (π g (e ((β i : fixedVectors ρ H.toSubgroup) : V)))) *
              ℓv.val (π g⁻¹ w)
          have key : π g (e ((β i : fixedVectors ρ H.toSubgroup) : V)) =
              e (ρ g ((β i : fixedVectors ρ H.toSubgroup) : V)) :=
            (Representation.IntertwiningMap.isIntertwining ρ π e.toIntertwiningMap g _).symm
          rw [key, Representation.Equiv.symm_apply_apply]
      rw [hfs, hsint]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    -- Sum over the basis: the vectors `Σ_i c_i β_i` reassemble `e_H e⁻¹ w`.
    let P := averageProjection ρ hρa.1 H (e.symm w)
    have hsum : ∑ i, (ℓi i).val (e.symm w) • ((β i : fixedVectors ρ H.toSubgroup) : V) =
        Compact.averageMap ρ hρa.1 H.1 H.2 (e.symm w) := by
      have h := β.sum_repr P
      have h' := congrArg (fun x : fixedVectors ρ H.toSubgroup => (x : V)) h
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
      rw [averageProjection_apply] at h'
      rw [← h']
      rfl
    have hcomm := Compact.averageMap_commute ρ π hρa.1 hπa.1 H.1 H.2 e.toIntertwiningMap
    have havg : e (Compact.averageMap ρ hρa.1 H.1 H.2 (e.symm w)) =
        Compact.averageMap π hπa.1 H.1 H.2 w := by
      have h := LinearMap.congr_fun hcomm (e.symm w)
      simpa using h
    have hfix : ℓv.val (Compact.averageMap π hπa.1 H.1 H.2 w) = b.inner v w := by
      refine Jacquet.map_averageMap_of_forall_eq π hπa.1 H.1 H.2 ℓv.val w (b.inner v w) ?_
      intro k
      change b.inner v (π k.val w) = b.inner v w
      have hk : π (k.val)⁻¹ v = v := hv ⟨(k.val)⁻¹, H.toSubgroup.inv_mem k.2⟩
      rw [← b.invariant (k.val)⁻¹ v (π k.val w), hk, Representation.inv_self_apply]
    have hlin : ∑ i, ℓv.val (e ((β i : fixedVectors ρ H.toSubgroup) : V)) *
        (ℓi i).val (e.symm w) = b.inner v w := by
      rw [← hfix, ← havg, ← hsum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    calc ∑ i, (d : ℂ)⁻¹ * ℓv.val (e ((β i : fixedVectors ρ H.toSubgroup) : V)) *
          (ℓi i).val (e.symm w)
        = (d : ℂ)⁻¹ * ∑ i, ℓv.val (e ((β i : fixedVectors ρ H.toSubgroup) : V)) *
            (ℓi i).val (e.symm w) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = (d : ℂ)⁻¹ * star (ℓ.val v) := by
          rw [hlin, ← hw]
          congr 1
          exact (b.conj_inner_symm v w).symm
  · rw [ite_eq_right hne]
    have hempty : IsEmpty (ρ.Equiv π) := not_nonempty_iff.mp hne
    refine Finset.sum_eq_zero fun i _ => ?_
    exact orthogonalityIntegral_eq_zero Z le_rfl μ hρχ hπχ hcof hsqρ hsqπ hiρ hiπ hempty _
      (ℓi i) w ℓv

end Schur

end Langlands.BaseChange
