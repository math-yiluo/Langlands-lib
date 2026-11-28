import Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.EqualChar
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal
import WeilConjectures.RingTheory.Valuation.ValuationIndependence
import Mathlib.RingTheory.Filtration

/-! # Regular local charts for complete discrete valuation rings of mixed characteristic -/

universe u w

open IsLocalRing Polynomial

namespace Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation

section Expansion

variable {Λ W' : Type*} [CommRing Λ] [CommRing W'] [IsLocalRing W'] (ψ : Λ →+* W') {ϖ : W'}

/-- If `ψ : Λ → W'` is surjective on residue fields and `ϖ` generates the maximal ideal of
`W'`, every element of `W'` has `ϖ`-adic expansions with digits in `ψ(Λ)` to every finite
order, all truncations of one sequence of digits. -/
theorem exists_digits (hres : Function.Surjective ((residue W').comp ψ))
    (hϖ : maximalIdeal W' = Ideal.span {ϖ}) (y : W') :
    ∃ (a : ℕ → Λ) (z : ℕ → W'),
      ∀ k, y = ∑ j ∈ Finset.range k, ψ (a j) * ϖ ^ j + ϖ ^ k * z k := by
  have hstep (x : W') : ∃ (b : Λ) (x' : W'), x = ψ b + ϖ * x' := by
    obtain ⟨b, hb⟩ := hres (residue W' x)
    have hmem : x - ψ b ∈ maximalIdeal W' := by
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact hb.symm
    rw [hϖ, Ideal.mem_span_singleton'] at hmem
    obtain ⟨x', hx'⟩ := hmem
    exact ⟨b, x', by rw [mul_comm, hx']; ring⟩
  choose b s hs using hstep
  refine ⟨fun j => b (s^[j] y), fun k => s^[k] y, fun k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    simp only at ih ⊢
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    calc y = ∑ j ∈ Finset.range k, ψ (b (s^[j] y)) * ϖ ^ j + ϖ ^ k * s^[k] y := ih
      _ = _ := by
        conv_lhs => rw [hs (s^[k] y)]
        ring

/-- Suppose `Λ` is `p`-adically precomplete, `W'` is a Noetherian local ring with maximal ideal
`(ϖ)`, and `Λ → W' → κ(W')` is surjective. If `ψ(p) = u ϖ^e` lies in `(ϖ)` with `u` a unit,
then every element of `W'` is `∑_{j < e} ψ(b_j) ϖ^j`. -/
theorem exists_fin_digits [IsNoetherianRing W'] {p : Λ}
    (hpc : IsPrecomplete (Ideal.span {p}) Λ) (hres : Function.Surjective ((residue W').comp ψ))
    (hϖ : maximalIdeal W' = Ideal.span {ϖ}) {e : ℕ} (u : W'ˣ) (hpe : ψ p = u * ϖ ^ e)
    (hpm : ψ p ∈ maximalIdeal W') (y : W') :
    ∃ b : Fin e → Λ, y = ∑ j : Fin e, ψ (b j) * ϖ ^ (j : ℕ) := by
  let _ : Algebra Λ W' := ψ.toAlgebra
  have hsmul (a : Λ) (x : W') : a • x = ψ a * x := by
    rw [Algebra.smul_def]
    rfl
  obtain ⟨b, hb⟩ := exists_sum_smul_add_pow_smul hpc (fun j : Fin e => ϖ ^ (j : ℕ)) (fun y => by
    obtain ⟨a, z, h⟩ := exists_digits ψ hres hϖ y
    refine ⟨fun j => a j, (↑u⁻¹ : W') * z e, ?_⟩
    have h1 : (p • ((↑u⁻¹ : W') * z e) : W') = ϖ ^ e * z e := by
      rw [hsmul, hpe]
      calc (↑u * ϖ ^ e) * (↑u⁻¹ * z e) = (↑u * ↑u⁻¹) * (ϖ ^ e * z e) := by ring
        _ = ϖ ^ e * z e := by rw [Units.mul_inv, one_mul]
    rw [h1]
    simp only [hsmul]
    rw [Fin.sum_univ_eq_sum_range (fun j => ψ (a j) * ϖ ^ j) e]
    exact h e) y
  refine ⟨b, ?_⟩
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal W') (maximalIdeal.isMaximal W').ne_top,
    Ideal.mem_iInf]
  intro N
  obtain ⟨z, hz⟩ := hb N
  have : y - ∑ j : Fin e, ψ (b j) * ϖ ^ (j : ℕ) = ψ p ^ N * z := by
    rw [hz]
    simp only [hsmul, map_pow]
    ring
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm N)

/-- Let `Λ` be a Noetherian local ring with maximal ideal `(p)`, `ψ : Λ → W'` a local map to a
domain `W'` with `ψ(p) = u ϖ^e`, `u` a unit and `ϖ` irreducible. If `∑_{j < e} ψ(c_j) ϖ^j = 0`
then all `c_j` vanish. -/
theorem eq_zero_of_fin_digits [IsDomain W'] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsLocalHom ψ]
    {p : Λ} (hp : maximalIdeal Λ = Ideal.span {p}) (hϖ : Irreducible ϖ) {e : ℕ} (u : W'ˣ)
    (hpe : ψ p = u * ϖ ^ e) (c : Fin e → Λ)
    (hc : ∑ j : Fin e, ψ (c j) * ϖ ^ (j : ℕ) = 0) : c = 0 := by
  have hp0 : ψ p ≠ 0 := by
    rw [hpe]
    exact mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  -- All digits of a vanishing expansion are divisible by `p`.
  have hA (c : Fin e → Λ) (hc : ∑ j : Fin e, ψ (c j) * ϖ ^ (j : ℕ) = 0) (j : Fin e) :
      c j ∈ Ideal.span {p} := by
    by_contra hj
    obtain ⟨j₀, hj₀, hmin⟩ :=
      WellFounded.has_min wellFounded_lt {j | c j ∉ Ideal.span {p}} ⟨j, hj⟩
    have hdvd (j : Fin e) (hj : j ≠ j₀) : ϖ ^ ((j₀ : ℕ) + 1) ∣ ψ (c j) * ϖ ^ (j : ℕ) := by
      rcases lt_or_gt_of_ne hj with hlt | hlt
      · have hmem : c j ∈ Ideal.span {p} := by
          by_contra h
          exact hmin j h hlt
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
        rw [← hd, map_mul, hpe]
        have hle : (j₀ : ℕ) + 1 ≤ e + j := by
          have := j₀.isLt
          omega
        have h2 : ψ d * (↑u * ϖ ^ e) * ϖ ^ (j : ℕ) = (ψ d * ↑u) * ϖ ^ (e + j) := by ring
        rw [h2]
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hle) _
      · have hle : (j₀ : ℕ) + 1 ≤ j := by
          have := Fin.lt_def.mp hlt
          omega
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hle) _
    have hsum := Finset.add_sum_erase Finset.univ (fun j : Fin e => ψ (c j) * ϖ ^ (j : ℕ))
      (Finset.mem_univ j₀)
    rw [hc] at hsum
    have hdvd₀ : ϖ ^ ((j₀ : ℕ) + 1) ∣ ψ (c j₀) * ϖ ^ (j₀ : ℕ) := by
      have : ψ (c j₀) * ϖ ^ (j₀ : ℕ) =
          -∑ j ∈ Finset.univ.erase j₀, ψ (c j) * ϖ ^ (j : ℕ) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hsum
      rw [this, dvd_neg]
      exact Finset.dvd_sum fun j hj => hdvd j (Finset.ne_of_mem_erase hj)
    rw [pow_succ, mul_comm (ψ (c j₀))] at hdvd₀
    have hdvd₁ : ϖ ∣ ψ (c j₀) := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).mp hdvd₀
    have hunit : IsUnit (ψ (c j₀)) := by
      have : IsUnit (c j₀) := by
        rw [← notMem_maximalIdeal, hp]
        exact hj₀
      exact this.map ψ
    exact hϖ.not_isUnit (isUnit_of_dvd_unit hdvd₁ hunit)
  -- Hence all digits are divisible by every power of `p`.
  have hB (n : ℕ) : ∀ c : Fin e → Λ, ∑ j : Fin e, ψ (c j) * ϖ ^ (j : ℕ) = 0 →
      ∀ j, c j ∈ Ideal.span {p} ^ n := by
    induction n with
    | zero =>
      intro c _ j
      simp
    | succ n ih =>
      intro c hc j
      choose d hd using fun j => Ideal.mem_span_singleton'.mp (hA c hc j)
      have hsum : ∑ j : Fin e, ψ (d j) * ϖ ^ (j : ℕ) = 0 := by
        have : ψ p * ∑ j : Fin e, ψ (d j) * ϖ ^ (j : ℕ) = 0 := by
          rw [Finset.mul_sum, ← hc]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hd j, map_mul]
          ring
        exact (mul_eq_zero.mp this).resolve_left hp0
      rw [← hd j, pow_succ]
      exact Ideal.mul_mem_mul (ih d hsum j) (Ideal.mem_span_singleton_self p)
  funext j
  have hne : Ideal.span {p} ≠ ⊤ := by
    rw [← hp]
    exact (maximalIdeal.isMaximal Λ).ne_top
  have hmem : c j ∈ ⨅ n, Ideal.span {p} ^ n := Ideal.mem_iInf.mpr fun n => hB n c hc j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne, Ideal.mem_bot] at hmem
  exact hmem

/-- Let `Λ` be a `p`-adically precomplete Noetherian local domain with maximal ideal `(p)`, and
`ψ : Λ → W'` a local map, surjective on residue fields, to a Noetherian local domain `W'` whose
maximal ideal is generated by the irreducible element `ϖ`, with `ψ(p) = u ϖ^e`, `u` a unit and
`e > 0`. Then `W'` is presented over `Λ` by `ϖ` and an Eisenstein polynomial
`F = X^e - p G(X)`: evaluation at `ϖ` maps `Λ[X]` onto `W'` with kernel `(F)`, and the constant
coefficient of `F` is not in `𝔪_Λ²`. -/
theorem exists_eisenstein_presentation [IsDomain Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsDomain W'] [IsNoetherianRing W'] [IsLocalHom ψ] {p : Λ}
    (hp : maximalIdeal Λ = Ideal.span {p}) (hpc : IsPrecomplete (Ideal.span {p}) Λ)
    (hres : Function.Surjective ((residue W').comp ψ))
    (hϖ : maximalIdeal W' = Ideal.span {ϖ}) (hϖi : Irreducible ϖ) {e : ℕ} (he : 0 < e)
    (u : W'ˣ) (hpe : ψ p = u * ϖ ^ e) :
    ∃ F : Λ[X], F.Monic ∧ eval₂ ψ ϖ F = 0 ∧ F.coeff 0 ∉ maximalIdeal Λ ^ 2 ∧
      (∀ y : W', ∃ q : Λ[X], eval₂ ψ ϖ q = y) ∧
      (∀ q : Λ[X], eval₂ ψ ϖ q = 0 → F ∣ q) := by
  classical
  have hϖm : ϖ ∈ maximalIdeal W' := by
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hpm : ψ p ∈ maximalIdeal W' := by
    rw [hpe]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hϖm e he)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hpe
    exact mul_ne_zero u.ne_zero (pow_ne_zero _ hϖi.ne_zero) hpe.symm
  have hψm (a : Λ) (ha : a ∈ maximalIdeal Λ) : ψ a ∈ maximalIdeal W' := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun h => ha (h.of_map ψ)
  obtain ⟨g, hg⟩ := exists_fin_digits ψ hpc hres hϖ u hpe hpm (↑u⁻¹ : W')
  set G : Λ[X] := ∑ j : Fin e, Polynomial.C (p * g j) * X ^ (j : ℕ) with hG
  have hGdeg : G.degree < e := degree_sum_fin_lt _
  have hFm : (X ^ e - G).Monic := monic_X_pow_sub hGdeg
  have hFdeg : (X ^ e - G).degree = (e : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  have hFϖ : eval₂ ψ ϖ (X ^ e - G) = 0 := by
    have h1 : eval₂ ψ ϖ G = ψ p * ↑u⁻¹ := by
      rw [hG, eval₂_finsetSum, hg, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eval₂_mul, eval₂_C, eval₂_X_pow, map_mul, mul_assoc]
    rw [eval₂_sub, eval₂_X_pow, h1, hpe]
    calc ϖ ^ e - ↑u * ϖ ^ e * ↑u⁻¹ = ϖ ^ e - (↑u * ↑u⁻¹) * ϖ ^ e := by ring
      _ = 0 := by rw [Units.mul_inv, one_mul, sub_self]
  refine ⟨X ^ e - G, hFm, hFϖ, ?_, ?_, ?_⟩
  · -- The constant coefficient is `-p g₀` with `g₀` a unit.
    have hcoeff : (X ^ e - G).coeff 0 = -(p * g ⟨0, he⟩) := by
      rw [coeff_sub, coeff_X_pow, ite_eq_right (Nat.ne_of_lt he), zero_sub, hG, finsetSum_coeff,
        Finset.sum_eq_single (⟨0, he⟩ : Fin e)]
      · rw [coeff_C_mul_X_pow, ite_eq_left rfl]
      · intro j _ hj
        rw [coeff_C_mul_X_pow, ite_eq_right]
        intro h
        exact hj (Fin.ext h.symm)
      · intro h
        exact (h (Finset.mem_univ _)).elim
    have hg0 : g ⟨0, he⟩ ∉ maximalIdeal Λ := by
      intro h0
      apply (maximalIdeal.isMaximal W').ne_top
      rw [Ideal.eq_top_iff_one, ← Units.inv_mul u, hg]
      refine Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun j _ => ?_)
      by_cases hj : (j : ℕ) = 0
      · have : j = ⟨0, he⟩ := Fin.ext hj
        subst this
        exact Ideal.mul_mem_right _ _ (hψm _ h0)
      · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hϖm _ (Nat.pos_of_ne_zero hj))
    rw [hcoeff, Ideal.neg_mem_iff, hp, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    rintro ⟨c, hc⟩
    apply hg0
    rw [hp, Ideal.mem_span_singleton']
    refine ⟨c, mul_left_cancel₀ hp0 ?_⟩
    linear_combination hc
  · intro y
    obtain ⟨b, hb⟩ := exists_fin_digits ψ hpc hres hϖ u hpe hpm y
    refine ⟨∑ j : Fin e, Polynomial.C (b j) * X ^ (j : ℕ), ?_⟩
    rw [hb, eval₂_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  · intro q hq
    rw [← modByMonic_eq_zero_iff_dvd hFm]
    set r := q %ₘ (X ^ e - G) with hr
    have hrdeg : r.degree < e := by
      rw [← hFdeg]
      exact degree_modByMonic_lt q hFm
    have hr0 : eval₂ ψ ϖ r = 0 := by
      have := modByMonic_add_div q (X ^ e - G)
      rw [← this, eval₂_add, eval₂_mul, hFϖ, zero_mul, add_zero] at hq
      exact hq
    by_contra hne
    have hnat : r.natDegree < e := (natDegree_lt_iff_degree_lt hne).mpr hrdeg
    rw [eval₂_eq_sum_range' ψ hnat, ← Fin.sum_univ_eq_sum_range (fun j => ψ (r.coeff j) * ϖ ^ j)]
      at hr0
    have hc := eq_zero_of_fin_digits ψ hp hϖi u hpe (fun j : Fin e => r.coeff j) hr0
    apply hne
    ext k
    rw [coeff_zero]
    by_cases hk : k < e
    · exact congrFun hc ⟨k, hk⟩
    · exact coeff_eq_zero_of_degree_lt (hrdeg.trans_le (by exact_mod_cast not_lt.mp hk))

end Expansion

/-- Let `W'` be a complete discrete valuation ring with uniformizer `ϖ` whose residue field has
characteristic `p` with `p ≠ 0` in `W'` (mixed characteristic). Then every map from a finite
type `ℤ`-algebra to `Frac W'` factors through a regular local chart. The presentation used is
`W' = Λ[X] ⧸ (F)` with `Λ` a Cohen ring of the residue field and `F` an Eisenstein polynomial. -/
theorem chartConclusion_mixedChar
    {W' : Type u} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W']
    [IsAdicComplete (maximalIdeal W') W'] {ϖ : W'} (hϖ : Irreducible ϖ)
    (p : ℕ) [CharP (ResidueField W') p] (hchar : (p : W') ≠ 0)
    (C : Type w) [CommRing C] [Algebra.FiniteType ℤ C] (F' : C →+* FractionRing W') :
    ChartConclusion W' C F' := by
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero (ResidueField W') p with h | h
    · exact h
    · subst h
      exact (hchar Nat.cast_zero).elim
  have hpW : (p : W') ∈ maximalIdeal W' := by
    rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  obtain ⟨Λ, _, hC, ⟨eΛ⟩⟩ := exists_cohenRing p hpp (ResidueField W')
  obtain ⟨ψ, hψ⟩ := IsLocalRing.exists_cohenRing_lift W' p Λ hC eΛ
  obtain ⟨_, _, _, hmax, hcomp⟩ := hC
  have hψa (a : Λ) : residue W' (ψ a) = eΛ (Ideal.Quotient.mk _ a) :=
    RingHom.congr_fun hψ a
  have : IsLocalHom ψ := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : a ∈ maximalIdeal Λ := h
    rw [hmax, ← Ideal.Quotient.eq_zero_iff_mem] at hm
    have : ψ a ∈ maximalIdeal W' := by
      rw [← residue_eq_zero_iff, hψa, hm, map_zero]
    exact this ha
  have hres : Function.Surjective ((residue W').comp ψ) := by
    rw [hψ, RingHom.coe_comp]
    exact eΛ.surjective.comp Ideal.Quotient.mk_surjective
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hchar hϖ
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [pow_zero, mul_one] at hv
      rw [hv] at hpW
      exact ((maximalIdeal.isMaximal W').ne_top (Ideal.eq_top_of_isUnit_mem _ hpW v.isUnit)).elim
    · exact h
  have hpe : ψ (p : Λ) = v * ϖ ^ n := by
    rw [map_natCast]
    exact hv
  obtain ⟨F, hFm, hFϖ, hF0, hsurj, hdvd⟩ :=
    exists_eisenstein_presentation ψ hmax inferInstance hres hϖ.maximalIdeal_eq hϖ hn v hpe
  have : CharP (ResidueField Λ) p :=
    (RingHom.charP_iff_charP (ResidueField.map ψ) p).mpr inferInstance
  exact chartConclusion_of_dvr hϖ (intCast_prime_cases p (Or.inr hmax.symm)) ψ F hFm hFϖ hF0
    hsurj hdvd C F'

/-- Every map from a finite type `ℤ`-algebra to the fraction field of a complete discrete
valuation ring `W'` factors through a regular local chart. -/
theorem chartConclusion_of_complete
    {W' : Type u} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W']
    [IsAdicComplete (maximalIdeal W') W'] {ϖ : W'} (hϖ : Irreducible ϖ)
    (C : Type w) [CommRing C] [Algebra.FiniteType ℤ C] (F' : C →+* FractionRing W') :
    ChartConclusion W' C F' := by
  by_cases hchar : ((ringChar (ResidueField W') : ℕ) : W') = 0
  · exact chartConclusion_equalChar hϖ hchar C F'
  · have := ringChar.charP (ResidueField W')
    exact chartConclusion_mixedChar hϖ (ringChar (ResidueField W')) hchar C F'

end Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation
