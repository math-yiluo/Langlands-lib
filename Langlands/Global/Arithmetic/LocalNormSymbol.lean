import Langlands.Global.Arithmetic.FrobeniusNormClass
import Langlands.Global.Arithmetic.NormCongruence
import Langlands.Global.AdelicFunctoriality.NormCompatibilityProof
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-! # The cyclotomic symbol of local norms lies in the Galois image

For a Galois extension `L / K` of number fields containing a primitive `m`-th root of unity
`ζ`, and a finite place `w` of `K` over `p`, the symbol `σ_p(N_{K_w/ℚ_p}(b))` of the local
norm of every `b ∈ K_wˣ` lies in the image of `Gal(L/K)` in `(ℤ/m)ˣ` (Artin–Tate VII §2).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension WithZero

namespace Langlands.Global.CyclotomicSymbol

/-- The primality certificate of an element of `Nat.Primes`, as an instance. -/
instance fact_prime_primes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

section Symbol

variable (m : ℕ) [NeZero m] {K : Type*} [Field K] [NumberField K]

/-- The cyclotomic symbol of the local norm at a finite place `w` of `K` above a place `p₀`
of `ℚ`: `b ↦ σ_p(N_{K_w/ℚ_p}(b))` with `p = primesEquiv p₀`. -/
def normSymbolAt (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver p₀.asIdeal] : (w.adicCompletion K)ˣ →* (ZMod m)ˣ :=
  (localSymbol m (Rat.HeightOneSpectrum.primesEquiv p₀)).comp
    (Units.map ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀).toRingEquiv.toMonoidHom.comp
      (Langlands.Global.AdelicFunctoriality.FiniteExtension.localNorm p₀ w)))

theorem normSymbolAt_apply (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver p₀.asIdeal] (b : (w.adicCompletion K)ˣ) :
    normSymbolAt m p₀ w b = localSymbol m (Rat.HeightOneSpectrum.primesEquiv p₀)
      (Units.map ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀).toRingEquiv.toMonoidHom.comp
        (Langlands.Global.AdelicFunctoriality.FiniteExtension.localNorm p₀ w)) b) := rfl

/-- The symbol of local norms is trivial near `1`. -/
theorem exists_nhds_normSymbolAt_eq_one (p₀ : HeightOneSpectrum (𝓞 ℚ))
    (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver p₀.asIdeal] :
    ∃ U ∈ 𝓝 (1 : w.adicCompletion K), ∀ b : (w.adicCompletion K)ˣ, (b : w.adicCompletion K) ∈ U →
      normSymbolAt m p₀ w b = 1 := by
  set p : ℕ := (Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)
  let f : w.adicCompletion K → ℚ_[p] := fun x =>
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀
      (Langlands.Global.AdelicFunctoriality.FiniteExtension.localNorm p₀ w x)
  have hf : Continuous f := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀).continuous.comp
    (Langlands.Global.AdelicFunctoriality.FiniteExtension.continuous_localNorm p₀ w)
  have hf1 : f 1 = 1 := by simp [f]
  set ε : ℝ := min ((p : ℝ) ^ (-(m.factorization p : ℤ))) (1 / 2)
  have hε : 0 < ε := lt_min (zpow_pos (by exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv p₀).2.pos) _)
    (by norm_num)
  refine ⟨f ⁻¹' Metric.ball 1 ε, hf.continuousAt.preimage_mem_nhds
    (by rw [hf1]; exact Metric.ball_mem_nhds 1 hε), fun b hb => ?_⟩
  have hb' : ‖f b - 1‖ < ε := by simpa [dist_eq_norm] using hb
  rw [normSymbolAt_apply]
  apply localSymbol_eq_one
  · exact (hb'.trans_le (min_le_left _ _)).le
  · exact hb'.trans_le ((min_le_right _ _).trans (by norm_num))

end Symbol

section Approximation

variable {K : Type*} [Field K] [NumberField K]

/-- An integer of `K` that is `w`-adically close enough to `z` lies in a prescribed
neighborhood of `z` in `K_w`. -/
theorem exists_pow_sub_mem_imp_mem (w : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K)
    {V : Set (w.adicCompletion K)} (hV : V ∈ 𝓝 (algebraMap K (w.adicCompletion K) z)) :
    ∃ N : ℕ, ∀ y : 𝓞 K, y - z ∈ w.asIdeal ^ N → algebraMap K (w.adicCompletion K) y ∈ V := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hV
  have h1 : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding : _ →*₀ ℤᵐ⁰).toMonoidHom γ)
  refine ⟨N, fun y hy => hγ ?_⟩
  change Valued.v.restrict (algebraMap K (w.adicCompletion K) y -
    algebraMap K (w.adicCompletion K) z) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← map_sub]
  refine lt_of_le_of_lt ?_ hN
  have hval : Valued.v (algebraMap K (w.adicCompletion K) ((y : K) - z)) =
      w.valuation K ((y : K) - z) := valuedAdicCompletion_eq_valuation' (v := w) _
  rw [hval, ← WithZero.exp_nsmul]
  have h2 := (intValuation_le_pow_iff_mem w (y - z) N).2 hy
  rw [← valuation_of_algebraMap (K := K)] at h2
  convert h2 using 2
  · push_cast
    rfl
  · simp

end Approximation

section Principal

open Langlands.Global.AdelicFunctoriality

variable {K : Type*} [Field K] [NumberField K]

/-- The product over the places `w | p₀` of the local norms of `α ∈ K` is `N_{K/ℚ}(α)` in
`ℚ_{p₀}` (the finite part of the Library's principal norm compatibility). -/
theorem prod_localNorm_algebraMap (p₀ : HeightOneSpectrum (𝓞 ℚ)) (α : K) :
    ∏ w : FinitePlacesAbove K p₀, FiniteExtension.localNorm p₀ w.1
        (algebraMap K (w.1.adicCompletion K) α) =
      algebraMap ℚ (p₀.adicCompletion ℚ) (Algebra.norm ℚ α) := by
  have h := (normCompatibility.{0, _}).2 ℚ K α
  have h' := congrArg (fun a : AdeleRing (𝓞 ℚ) ℚ => a.2 p₀) h
  change (finiteAdeleNorm (algebraMap K (FiniteAdeleRing (𝓞 K) K) α)) p₀ = _ at h'
  rw [finiteAdeleNorm_apply] at h'
  exact h'

/-- The symbol at `p` of the global norm is the product of the symbols of the local norms at
the places above `p`. -/
theorem ratLocalSymbol_norm_eq_prod (m : ℕ) [NeZero m] (p₀ : HeightOneSpectrum (𝓞 ℚ))
    (α : Kˣ) :
    ratLocalSymbol m (Rat.HeightOneSpectrum.primesEquiv p₀)
        (Units.map (Algebra.norm ℚ : K →* ℚ) α) =
      ∏ w : FinitePlacesAbove K p₀,
        normSymbolAt m p₀ w.1 (Units.map (algebraMap K (w.1.adicCompletion K)).toMonoidHom α) := by
  have key : Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀
      (∏ w : FinitePlacesAbove K p₀, FiniteExtension.localNorm p₀ w.1
        (algebraMap K (w.1.adicCompletion K) (α : K))) =
      ((Algebra.norm ℚ (α : K) : ℚ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)]) := by
    rw [prod_localNorm_algebraMap]
    exact ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀).toAlgEquiv.commutes _).trans
      (eq_ratCast _ _)
  simp only [normSymbolAt_apply]
  rw [← map_prod, ratLocalSymbol, MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [Units.coe_prod]
  exact key.symm.trans (map_prod (Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀) _ _)

end Principal

section CRT

open Langlands.Global.AdelicFunctoriality

variable {K : Type*} [Field K] [NumberField K]

theorem natCast_not_mem_of_coprime (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver p₀.asIdeal] {M : ℕ}
    (hM : Nat.Coprime (Rat.HeightOneSpectrum.primesEquiv p₀) M) :
    ((M : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro hmem
  have h1 : ((M : ℕ) : 𝓞 ℚ) ∈ p₀.asIdeal := by
    rw [Ideal.over_def w.asIdeal p₀.asIdeal, Ideal.mem_comap, map_natCast]
    exact hmem
  have h2 : Rat.HeightOneSpectrum.natGenerator p₀ ∣ M := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h1
    rwa [map_natCast] at this
  have h3 : Nat.Coprime (Rat.HeightOneSpectrum.natGenerator p₀) M := hM
  have h4 := Nat.Coprime.eq_one_of_dvd h3 h2
  exact (Rat.HeightOneSpectrum.prime_natGenerator p₀).one_lt.ne' h4

open Classical in
/-- Chinese remainder approximation at the places above `p₀` and modulo `M` prime to `p`:
there is `α ∈ 𝓞 K` with `α ≡ β` modulo `w^N`, `α ≡ 1` modulo `w'^N` for the other places
`w'` above `p₀`, and `α ≡ 1 mod M`. -/
theorem exists_crt (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : FinitePlacesAbove K p₀) (β : 𝓞 K)
    (N M : ℕ) (hM : Nat.Coprime (Rat.HeightOneSpectrum.primesEquiv p₀) M) :
    ∃ α : 𝓞 K, (∀ w' : FinitePlacesAbove K p₀,
        α - (if w' = w then β else 1) ∈ w'.1.asIdeal ^ N) ∧
      α - 1 ∈ Ideal.span {((M : ℕ) : 𝓞 K)} := by
  classical
  let I : Option (FinitePlacesAbove K p₀) → Ideal (𝓞 K) := fun i =>
    match i with
    | none => Ideal.span {((M : ℕ) : 𝓞 K)}
    | some w' => w'.1.asIdeal ^ N
  let x : Option (FinitePlacesAbove K p₀) → 𝓞 K := fun i =>
    match i with
    | none => 1
    | some w' => if w' = w then β else 1
  have hcopM : ∀ w' : FinitePlacesAbove K p₀,
      IsCoprime (Ideal.span {((M : ℕ) : 𝓞 K)}) (w'.1.asIdeal ^ N) := by
    intro w'
    have : w'.1.asIdeal.LiesOver p₀.asIdeal := w'.2
    have hnot := natCast_not_mem_of_coprime p₀ w'.1 hM
    have hmax : w'.1.asIdeal.IsMaximal := w'.1.isMaximal
    have hsup : w'.1.asIdeal ⊔ Ideal.span {((M : ℕ) : 𝓞 K)} = ⊤ :=
      hmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h =>
        hnot (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact (Ideal.isCoprime_iff_sup_eq.2 (by rw [sup_comm]; exact hsup)).pow_right
  have hI : Pairwise (Function.onFun IsCoprime I) := by
    intro i j hij
    match i, j with
    | none, none => exact absurd rfl hij
    | none, some w' => exact hcopM w'
    | some w', none => exact (hcopM w').symm
    | some w₁, some w₂ =>
      have hne : w₁.1.asIdeal ≠ w₂.1.asIdeal := fun h =>
        hij (congrArg some (Subtype.ext (HeightOneSpectrum.ext h)))
      have : w₁.1.asIdeal.IsMaximal := w₁.1.isMaximal
      have : w₂.1.asIdeal.IsMaximal := w₂.1.isMaximal
      exact (Ideal.isCoprime_of_isMaximal hne).pow
  obtain ⟨α, hα⟩ := Ideal.exists_forall_sub_mem_ideal hI x
  exact ⟨α, fun w' => hα (some w'), hα none⟩

end CRT

section Split

variable (m : ℕ) [NeZero m]

/-- The product of all local symbols splits into the factors in a finite set `S` and the
product outside `S`. -/
theorem symbolProduct_eq_mul (S : Finset ℕ) (x : ℚˣ) :
    symbolProduct m x =
      (∏ᶠ ℓ : Nat.Primes, if (ℓ : ℕ) ∈ S then primeSymbol m ℓ x else 1) *
        outsideSymbol m S x := by
  have h1 : (Function.mulSupport fun ℓ : Nat.Primes =>
      if (ℓ : ℕ) ∈ S then primeSymbol m ℓ x else 1).Finite := by
    refine (mulSupport_primeSymbol_finite m x).subset fun ℓ hℓ => ?_
    have hℓ' : (if (ℓ : ℕ) ∈ S then primeSymbol m ℓ x else 1) ≠ 1 := hℓ
    change primeSymbol m ℓ x ≠ 1
    by_cases h : (ℓ : ℕ) ∈ S
    · rwa [ite_eq_left h] at hℓ'
    · rw [ite_eq_right h] at hℓ'
      exact absurd rfl hℓ'
  rw [symbolProduct_apply, outsideSymbol_apply, ← finprod_mul_distrib h1
    ((mulSupport_primeSymbol_finite m x).subset (mulSupport_outside_subset m S x))]
  congr 1
  funext ℓ
  by_cases h : (ℓ : ℕ) ∈ S
  · rw [ite_eq_left h, ite_eq_left h, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, one_mul]

end Split

section Main

open Langlands.Global.AdelicFunctoriality

variable (m : ℕ) [NeZero m] {K : Type*} [Field K] [NumberField K]

/-- For a prime `ℓ ≠ p` dividing `m`, the symbol at `ℓ` of the norm of an algebraic integer
`≡ 1 mod (m₀)²` is trivial, where `m₀` is the prime-to-`p` part of `m`. -/
theorem primeSymbol_norm_eq_one (p : ℕ) [Fact p.Prime] (ℓ : Nat.Primes) (hℓp : (ℓ : ℕ) ≠ p)
    (hℓm : (ℓ : ℕ) ∣ m) (α : 𝓞 K)
    (hα : α - 1 ∈ Ideal.span {(((m / p ^ m.factorization p) ^ 2 : ℕ) : 𝓞 K)})
    (hN : (Algebra.norm ℚ (α : K)) ≠ 0) :
    primeSymbol m ℓ (Units.mk0 _ hN) = 1 := by
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 hα
  have hdvd := intNorm_sub_one_dvd ((m / p ^ m.factorization p) ^ 2) α β
    (by linear_combination -hβ)
  have hr : 0 < m.factorization ℓ :=
    Nat.Prime.factorization_pos_of_dvd ℓ.2 (NeZero.ne m) hℓm
  have hℓdvd : (ℓ : ℕ) ^ (m.factorization ℓ + 1) ∣ (m / p ^ m.factorization p) ^ 2 := by
    have h1 := ordProj_dvd_ordCompl m p ℓ.2 hℓp
    have h2 := pow_dvd_pow_of_dvd h1 2
    rw [← pow_mul] at h2
    exact (pow_dvd_pow _ (by omega)).trans h2
  have hz : ((Algebra.norm ℤ α : ℤ) : ℚ) ≠ 0 := by
    rw [Algebra.coe_norm_int]
    exact hN
  have hunit : Units.mk0 (Algebra.norm ℚ (α : K)) hN = Units.mk0 _ hz :=
    Units.ext (by rw [Units.val_mk0, Units.val_mk0, Algebra.coe_norm_int])
  rw [hunit]
  change ratLocalSymbol m ℓ _ = 1
  refine ratLocalSymbol_intCast_eq_one m ℓ _ hz ?_
  exact (Int.natCast_dvd_natCast.2 hℓdvd |>.trans (by exact_mod_cast hdvd))

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ m)

/-- The Artin–Tate norm theorem for global integers: for `β ∈ 𝓞 K` nonzero at a place `w`
above `p₀`, the symbol of the local norm of `β` lies in the Galois image. -/
theorem normSymbolAt_integral_mem (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : FinitePlacesAbove K p₀)
    (β : 𝓞 K) (hβ : algebraMap K (w.1.adicCompletion K) (β : K) ≠ 0) :
    normSymbolAt m p₀ w.1 (Units.mk0 _ hβ) ∈ galoisImage K hζ := by
  classical
  set p : ℕ := (Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ) with hp_def
  have hpprime : p.Prime := (Rat.HeightOneSpectrum.primesEquiv p₀).2
  -- the neighborhood at `w`
  obtain ⟨U, hU, hUs⟩ := exists_nhds_normSymbolAt_eq_one m p₀ w.1
  set b := algebraMap K (w.1.adicCompletion K) (β : K) with hb_def
  have hV : (fun x => x * b⁻¹) ⁻¹' U ∈ 𝓝 b := by
    refine (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds ?_
    simpa [mul_inv_cancel₀ hβ] using hU
  obtain ⟨N₀, hN₀⟩ := exists_pow_sub_mem_imp_mem w.1 β hV
  -- the neighborhoods at the other places above `p₀`
  have hother : ∀ w' : FinitePlacesAbove K p₀, ∃ N : ℕ, ∀ y : 𝓞 K,
      y - 1 ∈ w'.1.asIdeal ^ N → ∀ hy : algebraMap K (w'.1.adicCompletion K) (y : K) ≠ 0,
        normSymbolAt m p₀ w'.1 (Units.mk0 _ hy) = 1 := by
    intro w'
    obtain ⟨U', hU', hU's⟩ := exists_nhds_normSymbolAt_eq_one m p₀ w'.1
    obtain ⟨N, hN⟩ := exists_pow_sub_mem_imp_mem w'.1 1 (by simpa using hU')
    exact ⟨N, fun y hy hy0 => hU's _ (hN y hy)⟩
  choose N' hN' using hother
  set N : ℕ := N₀ + ∑ w', N' w' with hN_def
  have hN₀N : N₀ ≤ N := Nat.le_add_right _ _
  have hN'N : ∀ w', N' w' ≤ N := fun w' =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ w')).trans
      (Nat.le_add_left _ _)
  -- the Chinese remainder element
  set M : ℕ := (m / p ^ m.factorization p) ^ 2 with hM_def
  have hM : Nat.Coprime (Rat.HeightOneSpectrum.primesEquiv p₀) M :=
    (Nat.coprime_ordCompl hpprime (NeZero.ne m)).pow_right 2
  obtain ⟨α, hαw, hα1⟩ := exists_crt p₀ w β N M hM
  -- a positive integer in all the ideals
  set P : Ideal (𝓞 K) := ∏ w' : FinitePlacesAbove K p₀, w'.1.asIdeal ^ N with hP_def
  have hP0 : P ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w' _ => pow_ne_zero _ w'.1.ne_bot
  have hM0 : M ≠ 0 := pow_ne_zero 2 (Nat.pos_iff_ne_zero.1 (Nat.ordCompl_pos p (NeZero.ne m)))
  set T : ℕ := M * Ideal.absNorm P with hT_def
  have hTpos : 0 < T := Nat.mul_pos (Nat.pos_of_ne_zero hM0)
    (Nat.pos_of_ne_zero fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hTw : ∀ w' : FinitePlacesAbove K p₀, ((T : ℕ) : 𝓞 K) ∈ w'.1.asIdeal ^ N := by
    intro w'
    have h1 : ((Ideal.absNorm P : ℕ) : 𝓞 K) ∈ P := Ideal.absNorm_mem P
    have h2 : P ≤ w'.1.asIdeal ^ N :=
      Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ w'))
    rw [hT_def, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (h2 h1)
  have hTM : ((T : ℕ) : 𝓞 K) ∈ Ideal.span {((M : ℕ) : 𝓞 K)} := by
    rw [hT_def, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨k, hk⟩ := exists_norm_add_nsmul_pos (α : K) (T := (T : ℚ)) (by exact_mod_cast hTpos)
  set α' : 𝓞 K := α + ((k * T : ℕ) : 𝓞 K) with hα'_def
  have hα'K : ((α' : 𝓞 K) : K) = (α : K) + algebraMap ℚ K ((k : ℚ) * T) := by
    simp [hα'_def]
  have hNpos : 0 < Algebra.norm ℚ ((α' : 𝓞 K) : K) := by
    rw [hα'K]
    exact hk
  have hNne : Algebra.norm ℚ ((α' : 𝓞 K) : K) ≠ 0 := hNpos.ne'
  have hα'ne : ((α' : 𝓞 K) : K) ≠ 0 := fun h => hNne (by rw [h, Algebra.norm_zero])
  have hkT : ∀ I : Ideal (𝓞 K), ((T : ℕ) : 𝓞 K) ∈ I → ((k * T : ℕ) : 𝓞 K) ∈ I :=
    fun I hI => by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hI
  have hα'w : ∀ w' : FinitePlacesAbove K p₀,
      α' - (if w' = w then β else 1) ∈ w'.1.asIdeal ^ N := fun w' => by
    have h : α' - (if w' = w then β else 1) =
        (α - (if w' = w then β else 1)) + ((k * T : ℕ) : 𝓞 K) := by
      rw [hα'_def]
      ring
    rw [h]
    exact Ideal.add_mem _ (hαw w') (hkT _ (hTw w'))
  have hα'1 : α' - 1 ∈ Ideal.span {((M : ℕ) : 𝓞 K)} := by
    have h : α' - 1 = (α - 1) + ((k * T : ℕ) : 𝓞 K) := by
      rw [hα'_def]
      ring
    rw [h]
    exact Ideal.add_mem _ hα1 (hkT _ hTM)
  -- the product formula for `N(α')`
  set x : ℚˣ := Units.mk0 _ hNne with hx_def
  have hpf := product_formula m x
  have hsign : signUnit m x = 1 := by
    change (if (x : ℚ) < 0 then -1 else 1) = 1
    exact ite_eq_right (not_lt.2 hNpos.le)
  set S : Finset ℕ := (m * p).primeFactors with hS_def
  have hpS : p ∈ S := Nat.mem_primeFactors.2 ⟨hpprime, dvd_mul_left p m,
    mul_ne_zero (NeZero.ne m) hpprime.ne_zero⟩
  rw [hsign, one_mul, symbolProduct_eq_mul m S] at hpf
  have hinside : (∏ᶠ ℓ : Nat.Primes, if (ℓ : ℕ) ∈ S then primeSymbol m ℓ x else 1) =
      primeSymbol m (Rat.HeightOneSpectrum.primesEquiv p₀) x := by
    rw [finprod_eq_single _ (Rat.HeightOneSpectrum.primesEquiv p₀)]
    · exact ite_eq_left hpS
    · intro ℓ hℓ
      by_cases hℓS : (ℓ : ℕ) ∈ S
      · rw [ite_eq_left hℓS]
        have hℓp : (ℓ : ℕ) ≠ p := fun h => hℓ (Subtype.ext h)
        have hℓm : (ℓ : ℕ) ∣ m := by
          rcases (Nat.Prime.dvd_mul ℓ.2).1 (Nat.dvd_of_mem_primeFactors hℓS) with h | h
          · exact h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq ℓ.2 hpprime).1 h) hℓp
        exact primeSymbol_norm_eq_one m p ℓ hℓp hℓm α' hα'1 hNne
      · exact ite_eq_right hℓS
  -- the symbol at `p` as a product over the places above `p₀`
  set αu : Kˣ := Units.mk0 _ hα'ne with hαu_def
  have hσp : primeSymbol m (Rat.HeightOneSpectrum.primesEquiv p₀) x =
      ∏ w' : FinitePlacesAbove K p₀,
        normSymbolAt m p₀ w'.1 (Units.map (algebraMap K (w'.1.adicCompletion K)).toMonoidHom αu) := by
    rw [← ratLocalSymbol_norm_eq_prod m p₀ αu]
    rfl
  have hprod : (∏ w' : FinitePlacesAbove K p₀,
      normSymbolAt m p₀ w'.1 (Units.map (algebraMap K (w'.1.adicCompletion K)).toMonoidHom αu)) =
      normSymbolAt m p₀ w.1 (Units.map (algebraMap K (w.1.adicCompletion K)).toMonoidHom αu) := by
    refine Finset.prod_eq_single w (fun w' _ hw' => ?_) (fun h => absurd (Finset.mem_univ w) h)
    have hmem := hα'w w'
    rw [ite_eq_right hw'] at hmem
    have hy : algebraMap K (w'.1.adicCompletion K) ((α' : 𝓞 K) : K) ≠ 0 := by
      simpa using hα'ne
    have h1 := hN' w' α' (Ideal.pow_le_pow_right (hN'N w') hmem) hy
    rw [← h1]
    congr 1
    exact Units.ext rfl
  have hatw : normSymbolAt m p₀ w.1
      (Units.map (algebraMap K (w.1.adicCompletion K)).toMonoidHom αu) =
      normSymbolAt m p₀ w.1 (Units.mk0 _ hβ) := by
    have hmem := hα'w w
    rw [ite_eq_left rfl] at hmem
    have h1 := hN₀ α' (Ideal.pow_le_pow_right hN₀N hmem)
    set z : (w.1.adicCompletion K)ˣ :=
      Units.map (algebraMap K (w.1.adicCompletion K)).toMonoidHom αu * (Units.mk0 _ hβ)⁻¹
    have hz : normSymbolAt m p₀ w.1 z = 1 := hUs z h1
    rw [map_mul, map_inv, mul_inv_eq_one] at hz
    exact hz
  rw [hinside, hσp, hprod, hatw] at hpf
  -- the outside product lies in the Galois image
  have hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∈ S := fun ℓ hℓ hdvd =>
    Nat.mem_primeFactors.2 ⟨hℓ, dvd_mul_of_dvd_left hdvd p,
      mul_ne_zero (NeZero.ne m) hpprime.ne_zero⟩
  have hspan : Ideal.span {α'} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    exact hα'ne (by rw [h]; rfl)
  have hout := outsideSymbol_absNorm_mem m S K hζ hT (Ideal.span {α'}) hspan
  have hxeq : natUnit (Ideal.absNorm (Ideal.span {α'}))
      (fun h => hspan (Ideal.absNorm_eq_zero_iff.1 h)) = x := by
    apply Units.ext
    rw [natUnit, Units.val_mk0, hx_def, Units.val_mk0, Ideal.absNorm_span_singleton,
      ← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg]
    rw [Algebra.coe_norm_int]
    exact hNpos.le
  rw [hxeq] at hout
  rw [eq_inv_of_mul_eq_one_left hpf]
  exact Subgroup.inv_mem _ hout

/-- **Artin–Tate norm theorem.** For a Galois extension `L / K` of number fields containing a
primitive `m`-th root of unity `ζ`, and a finite place `w` of `K` above the place `p₀` of
`ℚ`, the cyclotomic symbol of the local norm of every `b ∈ K_wˣ` lies in the image of
`Gal(L/K)` in `(ℤ/m)ˣ`. -/
theorem normSymbolAt_mem_galoisImage (p₀ : HeightOneSpectrum (𝓞 ℚ))
    (w : FinitePlacesAbove K p₀) (b : (w.1.adicCompletion K)ˣ) :
    normSymbolAt m p₀ w.1 b ∈ galoisImage K hζ := by
  obtain ⟨U, hU, hUs⟩ := exists_nhds_normSymbolAt_eq_one m p₀ w.1
  -- an open neighborhood of `b` on which the symbol is constant
  have hV : (fun x => x * (b : w.1.adicCompletion K)⁻¹) ⁻¹' U ∩ {x | x ≠ 0} ∈
      𝓝 (b : w.1.adicCompletion K) := by
    refine Filter.inter_mem ?_ (isOpen_ne.mem_nhds b.ne_zero)
    refine (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds ?_
    simpa [mul_inv_cancel₀ b.ne_zero] using hU
  obtain ⟨y, hyV⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := K) w.1).mem_nhds hV
  have hy0 : algebraMap K (w.1.adicCompletion K) y ≠ 0 := hyV.2
  have hsame : normSymbolAt m p₀ w.1 b = normSymbolAt m p₀ w.1 (Units.mk0 _ hy0) := by
    have h1 := hUs (Units.mk0 _ hy0 * b⁻¹) (by
      rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
      exact hyV.1)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1.symm
  rw [hsame]
  -- write `y = a / d` with `a, d ∈ 𝓞 K`
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hd0 : (algebraMap (𝓞 K) K d) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)
  have hdw : algebraMap K (w.1.adicCompletion K) (d : K) ≠ 0 := by
    simpa using hd0
  have haw : algebraMap K (w.1.adicCompletion K) (a : K) ≠ 0 := by
    intro h
    apply hy0
    rw [map_div₀]
    change algebraMap K (w.1.adicCompletion K) (a : K) / _ = 0
    rw [h, zero_div]
  have hsplit : Units.mk0 _ hy0 = Units.mk0 _ haw * (Units.mk0 _ hdw)⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    rw [map_mul, map_inv₀]
  rw [hsplit, map_mul, map_inv]
  exact Subgroup.mul_mem _ (normSymbolAt_integral_mem m hζ p₀ w a haw)
    (Subgroup.inv_mem _ (normSymbolAt_integral_mem m hζ p₀ w d hdw))

end Main

end Langlands.Global.CyclotomicSymbol
