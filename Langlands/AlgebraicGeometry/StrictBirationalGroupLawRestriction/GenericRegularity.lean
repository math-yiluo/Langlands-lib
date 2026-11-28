import Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct
import Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat
import Langlands.AlgebraicGeometry.SmoothReducedBase

/-! # Generic regularity of a nonzerodivisor modulo extended ideals -/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction

/-- A nonzerodivisor `h` of a finite type algebra `B` over a noetherian domain `D` stays regular
modulo `𝔭 B`, for every ideal `𝔭` of `D`, after inverting one nonzero element `d` of `D`. -/
theorem exists_pow_mul_mem_map_of_mul_mem_map {D B : Type u} [CommRing D] [IsDomain D]
    [IsNoetherianRing D] [CommRing B] [Algebra D B] [Algebra.FiniteType D B]
    {h : B} (hh : h ∈ nonZeroDivisors B) :
    ∃ d : D, d ≠ 0 ∧ ∀ (𝔭 : Ideal D) (y : B), h * y ∈ 𝔭.map (algebraMap D B) →
      ∃ k : ℕ, algebraMap D B d ^ k * y ∈ 𝔭.map (algebraMap D B) := by
  obtain ⟨d, hd0, hflat⟩ := Module.Flat.exists_ne_zero_flat_localization_tensorProduct
    (A := D) (B := B) (M := B ⧸ Ideal.span {h})
  refine ⟨d, hd0, ?_⟩
  intro 𝔭 y hy
  set S := Submonoid.powers (algebraMap D B d) with hS
  let N := Localization S
  let M := B ⧸ Ideal.span {h}
  let f : N →ₗ[D] N := LinearMap.mulLeft D (algebraMap B N h)
  let g : N →ₗ[D] N ⊗[B] M :=
    ((TensorProduct.mk B N M).flip (Ideal.Quotient.mk (Ideal.span {h}) 1)).restrictScalars D
  let e := tensorQuotEquivQuotSMul N (Ideal.span {h})
  have he (n : N) : e (g n) = Submodule.Quotient.mk n := by
    change e (n ⊗ₜ Ideal.Quotient.mk (Ideal.span {h}) 1) = _
    rw [tensorQuotEquivQuotSMul_tmul_mk, one_smul]
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S n
    have h1 : IsLocalization.mk' N (h * b) s = 0 := by
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul]; exact hn
    rw [IsLocalization.mk'_eq_zero_iff] at h1 ⊢
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, (mem_nonZeroDivisors_iff.mp hh).1 _ (by rw [mul_left_comm]; exact hc)⟩
  have hfg : Function.Exact f g := by
    intro n
    rw [← (e.toEquiv.injective.eq_iff), LinearEquiv.coe_toEquiv, he, map_zero,
      Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [f, Algebra.smul_def]
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (e z)
    exact ⟨n, e.injective ((he n).trans hn)⟩
  have hinj := Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat f g hf hfg hg
    (D ⧸ 𝔭)
  have hmap : 𝔭.map (algebraMap D N) = (𝔭.map (algebraMap D B)).map (algebraMap B N) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmem (z : N) : (quotTensorEquivQuotSMul N 𝔭 ((1 : D ⧸ 𝔭) ⊗ₜ[D] z) = 0) ↔
      z ∈ (𝔭.map (algebraMap D B)).map (algebraMap B N) := by
    rw [quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map,
      hmap, Submodule.restrictScalars_mem]
  have hx : (1 : D ⧸ 𝔭) ⊗ₜ[D] algebraMap B N y = 0 := by
    apply hinj
    rw [map_zero, LinearMap.lTensor_tmul]
    apply (quotTensorEquivQuotSMul N 𝔭).injective
    rw [map_zero, hmem]
    have : f (algebraMap B N y) = algebraMap B N (h * y) := by
      simp [f, map_mul]
    rw [this]
    exact Ideal.mem_map_of_mem _ hy
  have hy' := (hmem _).mp (by rw [hx, map_zero])
  rw [IsLocalization.mem_map_algebraMap_iff S N] at hy'
  obtain ⟨⟨z, s⟩, hz⟩ := hy'
  rw [← map_mul, IsLocalization.eq_iff_exists S N] at hz
  obtain ⟨c, hc⟩ := hz
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp (S.mul_mem c.2 s.2)
  refine ⟨k, ?_⟩
  rw [hk]
  have : (↑c * ↑s) * y = ↑c * ↑z := by rw [← hc]; ring
  rw [this]
  exact Ideal.mul_mem_left _ _ z.2

/-- Let `T` be a smooth algebra over a noetherian ring `A`, let `P` be a prime of `A` and let `Z`
be an open subset of `Spec T` containing every prime of `T` that is minimal among the primes
lying over `P`. Then there is `a ∉ P` such that, for every prime `p ⊇ P` of `A` with `a ∉ p`,
`Z` contains every prime of `T` that is minimal among the primes lying over `p`. -/
theorem exists_notMem_forall_minimal_mem {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
    [IsNoetherianRing A] [Algebra.Smooth A T] (P : Ideal A) [P.IsPrime]
    (Z : Set (PrimeSpectrum T)) (hZ : IsOpen Z)
    (hP : ∀ Q : PrimeSpectrum T, Q.asIdeal.comap (algebraMap A T) = P →
      (∀ Q' : PrimeSpectrum T, Q' ≤ Q → Q'.asIdeal.comap (algebraMap A T) = P → Q' = Q) →
        Q ∈ Z) :
    ∃ a : A, a ∉ P ∧ ∀ Q : PrimeSpectrum T, P ≤ Q.asIdeal.comap (algebraMap A T) →
      a ∉ Q.asIdeal.comap (algebraMap A T) →
      (∀ Q' : PrimeSpectrum T, Q' ≤ Q →
        Q'.asIdeal.comap (algebraMap A T) = Q.asIdeal.comap (algebraMap A T) → Q' = Q) →
      Q ∈ Z := by
  classical
  set I := PrimeSpectrum.vanishingIdeal Zᶜ with hIdef
  have hZI (Q : PrimeSpectrum T) : Q ∈ Z ↔ ¬ I ≤ Q.asIdeal := by
    have hz : PrimeSpectrum.zeroLocus (I : Set T) = Zᶜ := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.isClosed_compl.closure_eq]
    rw [← not_iff_not, not_not, ← Set.mem_compl_iff, ← hz, PrimeSpectrum.mem_zeroLocus]
    rfl
  let D := A ⧸ P
  let B := T ⧸ P.map (algebraMap A T)
  let e : B ≃ₐ[D] D ⊗[A] T := Algebra.TensorProduct.quotIdealMapEquivQuotTensor T P
  have : Algebra.Smooth D (D ⊗[A] T) := Algebra.Smooth.baseChange A T D
  have : Algebra.Smooth D B := Algebra.Smooth.of_equiv e.symm
  have : Algebra.FiniteType D B := Algebra.FiniteType.equiv inferInstance e.symm
  have : Module.Flat D B := Module.Flat.of_linearEquiv e.toLinearEquiv
  have : IsReduced B := SmoothReducedBase.isReduced_of_smooth D B
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing D B
  let π : T →+* B := Ideal.Quotient.mk _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hkerπ : RingHom.ker π = P.map (algebraMap A T) := Ideal.mk_ker
  have hfin : (minimalPrimes B).Finite := minimalPrimes.finite_of_isNoetherianRing B
  -- No minimal prime of `B` contains the image of `I`.
  have hmin : ∀ 𝔮 ∈ minimalPrimes B, ¬ I.map π ≤ 𝔮 := by
    intro 𝔮 h𝔮
    have : 𝔮.IsPrime := h𝔮.1.1
    let Q₀ : PrimeSpectrum T := ⟨𝔮.comap π, inferInstance⟩
    have hker : P.map (algebraMap A T) ≤ Q₀.asIdeal := by
      rw [← hkerπ]; exact Ideal.ker_le_comap π
    have hcomap : Q₀.asIdeal.comap (algebraMap A T) = P := by
      apply le_antisymm
      · intro a ha
        by_contra haP
        have hd : Ideal.Quotient.mk P a ∈ nonZeroDivisors D :=
          mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
        have hreg : IsSMulRegular B (Ideal.Quotient.mk P a) :=
          Module.Flat.isSMulRegular_of_nonZeroDivisors hd
        have hnzd : algebraMap D B (Ideal.Quotient.mk P a) ∈ nonZeroDivisors B := by
          rw [mem_nonZeroDivisors_iff_right]
          intro z hz
          apply hreg
          simpa [Algebra.smul_def, mul_comm] using hz
        have hmem : algebraMap D B (Ideal.Quotient.mk P a) ∈ 𝔮 := ha
        exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔮)
          hmem hnzd
      · exact Ideal.map_le_iff_le_comap.mp hker
    have hQ₀ : Q₀ ∈ Z := by
      refine hP Q₀ hcomap fun Q' hQ' hQ'c => ?_
      have hker' : RingHom.ker π ≤ Q'.asIdeal := by
        rw [hkerπ, Ideal.map_le_iff_le_comap, hQ'c]
      have : (Q'.asIdeal.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hker'
      have hle : Q'.asIdeal.map π ≤ 𝔮 := Ideal.map_le_iff_le_comap.mpr hQ'
      have hge : 𝔮 ≤ Q'.asIdeal.map π := h𝔮.2 ⟨inferInstance, bot_le⟩ hle
      apply PrimeSpectrum.ext
      change Q'.asIdeal = 𝔮.comap π
      rw [← le_antisymm hle hge, Ideal.comap_map_of_surjective' π hπ, sup_eq_left.mpr hker']
    intro hle
    exact (hZI Q₀).mp hQ₀ (Ideal.map_le_iff_le_comap.mp hle)
  -- Prime avoidance gives an element of `I` regular on `B`.
  obtain ⟨hbar, hhI, hhnot⟩ : ∃ x ∈ I.map π, ∀ 𝔮 ∈ minimalPrimes B, x ∉ 𝔮 := by
    by_contra hcon
    push Not at hcon
    have hsub : ((I.map π : Ideal B) : Set B) ⊆
        ⋃ 𝔮 ∈ (hfin.toFinset : Set (Ideal B)), ((id 𝔮 : Ideal B) : Set B) := by
      intro x hx
      obtain ⟨𝔮, h𝔮, hx𝔮⟩ := hcon x hx
      exact Set.mem_biUnion (by simpa using h𝔮) hx𝔮
    obtain ⟨𝔮, h𝔮, hle⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun i hi _ _ => (hfin.mem_toFinset.mp hi).1.1)).mp hsub
    exact hmin 𝔮 (hfin.mem_toFinset.mp h𝔮) hle
  obtain ⟨h, hhI', rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hhI
  have hnzd : π h ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have hz' : z ∈ sInf (minimalPrimes B) := Submodule.mem_sInf.mpr fun 𝔮 h𝔮 => by
      have := h𝔮.1.1.mem_or_mem
        (show z * π h ∈ 𝔮 by rw [hz]; exact 𝔮.zero_mem)
      exact this.resolve_right (hhnot 𝔮 h𝔮)
    rw [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced] at hz'
    simpa using hz'
  obtain ⟨d, hd0, hd⟩ := exists_pow_mul_mem_map_of_mul_mem_map (D := D) hnzd
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨a, by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at hd0, ?_⟩
  intro Q hPQ ha hQmin
  rw [hZI]
  intro hIQ
  have hhQ : h ∈ Q.asIdeal := hIQ hhI'
  set p := Q.asIdeal.comap (algebraMap A T) with hp
  set J := p.map (algebraMap A T) with hJ
  have hJQ : J ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.mpr le_rfl
  have hQJ : Q.asIdeal ∈ J.minimalPrimes := by
    refine ⟨⟨Q.isPrime, hJQ⟩, fun Q' hQ' hQ'Q => ?_⟩
    have hc : Q'.comap (algebraMap A T) = p :=
      le_antisymm (Ideal.comap_mono hQ'Q) (Ideal.map_le_iff_le_comap.mp hQ'.2)
    have := hQmin ⟨Q', hQ'.1⟩ hQ'Q hc
    rw [← this]
  have hPJ : P.map (algebraMap A T) ≤ J := Ideal.map_mono hPQ
  have hJB : (p.map (Ideal.Quotient.mk P)).map (algebraMap D B) = J.map π := by
    rw [Ideal.map_map, Ideal.map_map]
    rfl
  have key : ∀ z : T, h * z ∈ J → ∃ k : ℕ, algebraMap A T a ^ k * z ∈ J := by
    intro z hz
    obtain ⟨k, hk⟩ := hd (p.map (Ideal.Quotient.mk P)) (π z)
      (by rw [hJB, ← map_mul]; exact Ideal.mem_map_of_mem _ hz)
    refine ⟨k, ?_⟩
    rw [hJB] at hk
    have hk' : π (algebraMap A T a ^ k * z) ∈ J.map π := by
      rw [map_mul, map_pow]; exact hk
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' π hπ, hkerπ, sup_eq_left.mpr hPJ] at hk'
    exact hk'
  have hex : ∃ n : ℕ, ∃ t : T, t ∉ Q.asIdeal ∧ t * h ^ n ∈ J := by
    let Tq := Localization.AtPrime Q.asIdeal
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes Tq Q.asIdeal J hQJ
    have hmem : algebraMap T Tq h ∈ (J.map (algebraMap T Tq)).radical := by
      rw [hrad]; exact Ideal.mem_map_of_mem _ hhQ
    obtain ⟨n, hn⟩ := hmem
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff Q.asIdeal.primeCompl Tq] at hn
    obtain ⟨⟨j, s⟩, hjs⟩ := hn
    rw [← map_mul, IsLocalization.eq_iff_exists Q.asIdeal.primeCompl Tq] at hjs
    obtain ⟨c, hc⟩ := hjs
    refine ⟨n, c * s, Q.asIdeal.primeCompl.mul_mem c.2 s.2, ?_⟩
    have : (↑c * ↑s) * h ^ n = ↑c * ↑j := by rw [← hc]; ring
    rw [this]; exact J.mul_mem_left _ j.2
  obtain ⟨t, htQ, htn⟩ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, mul_one] at htn
    exact htQ (hJQ htn)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hm] at htn
  obtain ⟨k, hk⟩ := key (t * h ^ m) (by rw [pow_succ] at htn; convert htn using 1; ring)
  have hlt : m < Nat.find hex := by omega
  apply Nat.find_min hex hlt
  refine ⟨algebraMap A T a ^ k * t, ?_, by rw [mul_assoc]; exact hk⟩
  have haQ : algebraMap A T a ∉ Q.asIdeal := ha
  exact Q.isPrime.mul_notMem (fun hpow => haQ (Q.isPrime.mem_of_pow_mem _ hpow)) htQ

end Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction
