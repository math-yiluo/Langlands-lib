import Langlands.Representation.Jacquet.StablePairingUniformAsymptotics

/-! # A fixed-dimensional threshold for actual stable-pairing ray asymptotics -/

noncomputable section

namespace Langlands.Jacquet.StablePairingData

open scoped NNReal

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The stable-pairing coefficient equality holds at every inverse contracting
power with exponent at least `d`, uniformly for the `K`-fixed vectors and
smooth functionals. -/
abbrev HasStablePairingRayAsymptoticsFrom (D : StablePairingData G)
    (ρ : Representation ℂ G V)
    (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ]
      Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ)
    (K : OpenSubgroup G) (d : ℕ) : Prop :=
  ∀ {v : V}, v ∈ fixedVectors ρ K.toSubgroup →
    ∀ {ℓ : SmoothDual ρ}, ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup →
      ∀ {r : ℕ}, d ≤ r →
        smoothDualPairing ρ ℓ (ρ (D.g⁻¹ ^ r) v) =
          b (Jacquet.mk (smoothContragredient ρ) D.N ℓ)
            (Jacquet.mk ρ D.Nbar (ρ (D.g⁻¹ ^ r) v))

variable {D : StablePairingData G} {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
  {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ]
    Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- At a good fixed level, the stable-pairing power asymptotic formula holds
from any upper bound on the fixed-space dimension. The threshold is independent
of the source vector, functional, and any other parameters of the action. -/
theorem IsStablePairing.pow_asymptotics_of_finrank_le
    (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b)
    (K : OpenSubgroup G) (hK : D.Good K)
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)]
    {d : ℕ} (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d) :
    D.HasStablePairingRayAsymptoticsFrom ρ b K d := by
  intro v hv ℓ hℓ r hr
  let C := compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹
  obtain ⟨t, ht, hmk⟩ := D.exists_stable_mk_eq hA hK ⟨v, hv⟩
  have hker : (⟨v, hv⟩ : fixedVectors ρ K.toSubgroup) - t ∈
      LinearMap.ker (fixedJacquetMap ρ D.Nbar D.M D.hMNbar K.toSubgroup) := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact Subtype.ext hmk.symm
  have hpk := hA.lower_kernel K hK hker
  have hmono : Monotone fun n : ℕ => LinearMap.ker (C ^ n) := by
    intro n m hnm x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← Nat.sub_add_cancel hnm, pow_add, Module.End.mul_apply, hx, map_zero]
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hpk
  have hfin := Module.End.ker_pow_le_ker_pow_finrank C n hn
  have hCr : (C ^ r) ⟨v, hv⟩ = (C ^ r) t := by
    have h0 := hmono (hd.trans hr) hfin
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
    exact h0
  have hstr : ∀ n : ℕ, (C ^ n) t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ := by
    intro n
    induction n with
    | zero => simpa using ht
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact compressedAction_mem_stableImage ρ hρ K _ D.g⁻¹ _ ih
  have hM : ∀ m ∈ D.M, m * D.g⁻¹ ^ r = D.g⁻¹ ^ r * m :=
    fun m hm => D.commute_pow m hm r
  have hup : ∀ u ∈ K, u ∈ D.N → (D.g⁻¹ ^ r)⁻¹ * u * D.g⁻¹ ^ r ∈ K := by
    intro u hu huN
    rw [inv_pow, inv_inv]
    exact D.upper_conj K hK u hu huN r
  have e₁ : ((C ^ r) ⟨v, hv⟩ : V) =
      Compact.averageMap ρ hρ K (D.isCompact K hK) (ρ (D.g⁻¹ ^ r) v) :=
    D.compressedAction_inv_pow_apply ρ hρ K hK r ⟨v, hv⟩
  rw [← smoothDualPairing_averageMap ρ hρ K (D.isCompact K hK) hℓ,
    ← D.mk_averageMap_apply ρ hρ K hK hM hup hv, ← e₁, hCr]
  exact (hb K hK ⟨ℓ, hℓ⟩ _ (hstr r)).symm

/-- The same uniform threshold for the normalized constant-term coefficient,
with the original chosen normalizing character. -/
theorem IsStablePairing.normalized_pow_asymptotics_of_finrank_le
    (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b)
    (δ : D.M →* ℝ≥0ˣ) (m : D.M) (hm : (m : G) = D.g⁻¹)
    (K : OpenSubgroup G) (hK : D.Good K)
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)]
    {d : ℕ} (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup)
    {r : ℕ} (hr : d ≤ r) :
    smoothDualPairing ρ ℓ (ρ ((m ^ r : D.M) : G) v) =
      ((NNReal.sqrt (δ (m ^ r) : ℝ≥0) : ℝ) : ℂ) *
        D.coefficientConstantTerm ρ b δ ℓ v (m ^ r) := by
  have h := hb.pow_asymptotics_of_finrank_le hA K hK hd hv hℓ hr
  have hm' : D.g⁻¹ ^ r = ((m ^ r : D.M) : G) := by
    rw [Subgroup.coe_pow, hm]
  rw [hm'] at h
  rw [h]
  exact apply_mk_eq_sqrt_mul_normalized δ _ (m ^ r) v

end Langlands.Jacquet.StablePairingData
