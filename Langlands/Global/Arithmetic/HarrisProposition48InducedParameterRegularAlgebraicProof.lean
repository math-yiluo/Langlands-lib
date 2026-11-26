import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement
import Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm

/-!
# Regular algebraicity from the induced complex-place parameters in Proposition 4.8

Proof of `Langlands.Global.Harris.Proposition48InducedParameterRegularAlgebraicStatement`.

Let `ξ` be a Hecke character of the CM field `E'`, algebraic after the twist of parity
`n - 1` for `n = [E' : E]`, relatively regular and conjugate inverse. At a place `w` of `E'`
above a complex place `v` of `E`, an actual parameter `d` of `ξ` has exponent `0` (conjugate
inversion) and weight of the parity of `n - 1` (the twisted algebraicity), and the parameters at
different places above `v`, read in the coordinate of `v`, have different weights (relative
regularity). Since `n` places lie above `v`, the induced list is Clozel regular algebraic of
rank `n`, and the archimedean bridge turns this into regular algebraicity of a cuspidal class
with these parameters; the length of its parameter lists identifies its rank with `n`.
-/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Global.Harris.InducedParameterRegularAlgebraic

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.LocalFactor.Archimedean
open Langlands.Global.AdelicFunctoriality

/-! ## Two uniqueness lemmas for complex powers -/

/-- If `r ^ s = 1` for every positive real `r`, then `s = 0`. -/
theorem eq_zero_of_forall_cpow_eq_one {s : ℂ}
    (h : ∀ r : ℝ, 0 < r → ((r : ℂ) ^ s) = 1) : s = 0 := by
  set t : ℝ := 1 / (‖s‖ + 1) with ht
  have htpos : 0 < t := by positivity
  have h1 := h (Real.exp t) (Real.exp_pos t)
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hnorm : ‖(t : ℂ) * s‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le, ht,
      div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  have hn0 : n = 0 := by
    by_contra hne
    have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne
    have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_two]
      ring
    rw [hn, h3] at hnorm
    nlinarith [Real.pi_gt_three]
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul, mul_eq_zero, Complex.ofReal_eq_zero] at hn
  rcases hn with h0 | h0
  · exact absurd h0 htpos.ne'
  · exact h0

/-- If `z ^ m = 1` for every complex `z` of norm one, then `m = 0`. -/
theorem eq_zero_of_forall_norm_eq_one_zpow_eq_one {m : ℤ}
    (h : ∀ z : ℂ, ‖z‖ = 1 → z ^ m = 1) : m = 0 := by
  by_contra hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hz := h (Complex.exp (((Real.pi / m : ℝ) : ℂ) * Complex.I))
    (Complex.norm_exp_ofReal_mul_I _)
  rw [← Complex.exp_int_mul] at hz
  have hmul : (m : ℂ) * (((Real.pi / m : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [hmul, Complex.exp_pi_mul_I] at hz
  norm_num at hz

/-! ## Character data of an algebraic conjugate-inverse character -/

/-- Character data `d` with `d(z) |z|^a = z^p z̄^q` and `d(z̄) = d(z)⁻¹` for all `z ∈ ℂˣ` have
exponent `0` and weight `p - q`, and `p + q = a`. -/
theorem characterData_of_twist_conj (d : ComplexCharacterData) (a : ℕ) (p q : ℤ)
    (hB : ∀ z : ℂˣ, (d.character z : ℂ) * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ a =
      (z : ℂ) ^ p * star (z : ℂ) ^ q)
    (hC : ∀ z : ℂˣ, (d.character (complexConjugation z) : ℂ) = (d.character z : ℂ)⁻¹) :
    d.exponent = 0 ∧ d.weight = p - q ∧ p + q = a := by
  -- the exponent
  have hexp : d.exponent = 0 := by
    have h4 : (2 : ℂ) * (2 * d.exponent) = 0 := by
      apply eq_zero_of_forall_cpow_eq_one
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      set z : ℂˣ := Units.mk0 (r : ℂ) hr0
      have hzc : complexConjugation z = z := by
        apply Units.ext
        rw [coe_complexConjugation]
        exact Complex.conj_ofReal r
      have hc := hC z
      rw [hzc] at hc
      have hnorm : ((‖(z : ℂ)‖ : ℝ) : ℂ) = (r : ℂ) := by
        change ((‖(r : ℂ)‖ : ℝ) : ℂ) = (r : ℂ)
        rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
      have hval : (d.character z : ℂ) = (r : ℂ) ^ (2 * d.exponent) := by
        rw [d.character_eq, hnorm]
        change ((r : ℂ) / (r : ℂ)) ^ d.weight * _ = _
        rw [div_self hr0, one_zpow, one_mul]
      have hne : (d.character z : ℂ) ≠ 0 := (d.character z).ne_zero
      have hsq : (d.character z : ℂ) ^ 2 = 1 := by
        have h1 : (d.character z : ℂ) * (d.character z : ℂ) = 1 := by
          calc (d.character z : ℂ) * (d.character z : ℂ)
              = (d.character z : ℂ) * (d.character z : ℂ)⁻¹ := by rw [← hc]
            _ = 1 := mul_inv_cancel₀ hne
        rw [sq]
        exact h1
      rw [show (2 : ℂ) * (2 * d.exponent) = ((2 : ℕ) : ℂ) * (2 * d.exponent) by norm_num,
        Complex.cpow_nat_mul, ← hval]
      exact hsq
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have := mul_eq_zero.mp h4
    rcases this with h | h
    · exact absurd h h2
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h2
      · exact h'
  -- the weight
  have hweight : d.weight = p - q := by
    have h0 : d.weight - (p - q) = 0 := by
      apply eq_zero_of_forall_norm_eq_one_zpow_eq_one
      intro z hz
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hz
        exact zero_ne_one hz
      set u : ℂˣ := Units.mk0 z hz0
      have hnorm : ((‖(u : ℂ)‖ : ℝ) : ℂ) = 1 := by
        change ((‖z‖ : ℝ) : ℂ) = 1
        rw [hz, Complex.ofReal_one]
      have hval : (d.character u : ℂ) = z ^ d.weight := by
        rw [d.character_eq, hnorm, div_one, Complex.one_cpow, mul_one]
        rfl
      have hstar : star z = z⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have hm : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
          rw [mul_comm]
          exact Complex.mul_conj z
        rw [hm, Complex.normSq_eq_norm_sq, hz]
        norm_num
      have hb := hB u
      rw [hval, hnorm, one_pow, mul_one] at hb
      change z ^ d.weight = z ^ p * star z ^ q at hb
      rw [hstar, inv_zpow', ← zpow_add₀ hz0] at hb
      rw [zpow_sub₀ hz0, hb, ← sub_eq_add_neg, div_self (zpow_ne_zero _ hz0)]
    omega
  -- the sum of the exponents
  have hsum : p + q = a := by
    set u : ℂˣ := Units.mk0 (2 : ℂ) two_ne_zero
    have hnorm : ((‖(u : ℂ)‖ : ℝ) : ℂ) = 2 := by
      change ((‖(2 : ℂ)‖ : ℝ) : ℂ) = 2
      rw [Complex.norm_two, Complex.ofReal_ofNat]
    have hval : (d.character u : ℂ) = 1 := by
      rw [d.character_eq, hnorm, hexp, mul_zero, Complex.cpow_zero, mul_one]
      change ((2 : ℂ) / 2) ^ d.weight = 1
      rw [div_self two_ne_zero, one_zpow]
    have hb := hB u
    rw [hval, hnorm, one_mul] at hb
    change (2 : ℂ) ^ a = (2 : ℂ) ^ p * star (2 : ℂ) ^ q at hb
    have hs2 : star (2 : ℂ) = 2 := by
      rw [Complex.star_def, map_ofNat]
    rw [hs2, ← zpow_add₀ two_ne_zero, ← zpow_natCast] at hb
    have hR : ((2 : ℝ) ^ (a : ℤ) : ℝ) = (2 : ℝ) ^ (p + q) := by
      have := congrArg (fun x : ℂ => ‖x‖) hb
      simpa [norm_zpow, Complex.norm_two] using this
    exact ((zpow_right_inj₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp hR).symm
  exact ⟨hexp, hweight, hsum⟩

/-! ## One infinite place of a Hecke character -/

section Place

variable {L : Type*} [Field L] [NumberField L]

omit [NumberField L] in
/-- Every unit of `ℂ` is the coordinate of a unit of the completion at a complex place. -/
theorem exists_units_map_extensionEmbedding {w : InfinitePlace L} (hw : w.IsComplex) (z : ℂˣ) :
    ∃ y : (InfiniteCompletion L w)ˣ, Units.map (extensionEmbedding w).toMonoidHom y = z := by
  let e := ringEquivComplexOfIsComplex hw
  refine ⟨Units.map e.symm.toMonoidHom z, ?_⟩
  apply Units.ext
  exact e.apply_symm_apply (z : ℂ)

/-- The twisted algebraicity equation at one place: if `ξ_∞ · ∏_τ |x_τ|^a` is the character of
the infinity type `t`, then `ξ_w(y) |y|^a = y^(t σ) ȳ^(t σ̄)` in the coordinate of `w`, where
`σ` is the embedding of `w`. -/
theorem infiniteComponent_mul_norm_pow [IsTotallyComplex L] {ξ : HeckeCharacter L} {a : ℕ}
    (t : InfinityType L)
    (ht : ∀ x : (InfiniteAdeles L)ˣ, (ξ.atInfinity x : ℂ) *
        ∏ τ : InfinitePlace L, ((‖(InfinityType.coordinate τ x : ℂ)‖ : ℝ) : ℂ) ^ a =
      (InfinityType.toCharacter t x : ℂ))
    (w : InfinitePlace L) (y : (InfiniteCompletion L w)ˣ) :
    (ξ.infiniteComponent w y : ℂ) * ((‖extensionEmbedding w (y : w.Completion)‖ : ℝ) : ℂ) ^ a =
      extensionEmbedding w (y : w.Completion) ^ t w.embedding *
        star (extensionEmbedding w (y : w.Completion)) ^
          t (ComplexEmbedding.conjugate w.embedding) := by
  classical
  set x : (InfiniteAdeles L)ˣ := Units.map (InfiniteAdeleRing.ofCompletion w) y with hx
  have hi : infiniteIdelesInclusion L x = infiniteIdeleInclusion L w y := Units.ext rfl
  have h1 : ξ.infiniteComponent w y = ξ.atInfinity x := by
    change ξ (ideleClassMap L (infiniteIdeleInclusion L w y)) =
      ξ (ideleClassMap L (infiniteIdelesInclusion L x))
    rw [hi]
  have hcw : (InfinityType.coordinate w x : ℂ) = extensionEmbedding w (y : w.Completion) := by
    rw [InfinityType.coordinate_apply]
    change extensionEmbedding w (InfiniteAdeleRing.ofCompletion w (y : w.Completion) w) = _
    rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_same]
  have hc : ∀ τ, τ ≠ w → InfinityType.coordinate τ x = 1 := by
    intro τ hτ
    apply Units.ext
    rw [InfinityType.coordinate_apply]
    change extensionEmbedding τ (InfiniteAdeleRing.ofCompletion w (y : w.Completion) τ) = 1
    rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hτ, map_one]
  have hprod1 : ∏ τ : InfinitePlace L, ((‖(InfinityType.coordinate τ x : ℂ)‖ : ℝ) : ℂ) ^ a =
      ((‖extensionEmbedding w (y : w.Completion)‖ : ℝ) : ℂ) ^ a := by
    rw [Finset.prod_eq_single w]
    · rw [hcw]
    · intro τ _ hτ
      rw [hc τ hτ]
      simp
    · intro hw
      exact absurd (Finset.mem_univ w) hw
  have hprod2 : (InfinityType.toCharacter t x : ℂ) =
      extensionEmbedding w (y : w.Completion) ^ t w.embedding *
        star (extensionEmbedding w (y : w.Completion)) ^
          t (ComplexEmbedding.conjugate w.embedding) := by
    rw [InfinityType.toCharacter_apply, Units.coe_prod, Finset.prod_eq_single w]
    · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.coe_star,
        hcw]
    · intro τ _ hτ
      rw [hc τ hτ]
      simp
    · intro hw
      exact absurd (Finset.mem_univ w) hw
  have h := ht x
  rw [← h1, hprod1, hprod2] at h
  exact h

/-- Conjugate inversion at one place: if `y'` has at `w` the complex-conjugate coordinate of
`y`, then `ξ_w(y') = ξ_w(y)⁻¹`. -/
theorem infiniteComponent_of_coordinate_conj [IsCMField L] {ξ : HeckeCharacter L}
    (hξ : IsConjugateInverse ξ) (w : InfinitePlace L) (y y' : (InfiniteCompletion L w)ˣ)
    (hy : extensionEmbedding w (y' : w.Completion) =
      star (extensionEmbedding w (y : w.Completion))) :
    ξ.infiniteComponent w y' = (ξ.infiniteComponent w y)⁻¹ := by
  classical
  have key : ideleEquiv (IsCMField.complexConj L).toRingEquiv (infiniteIdeleInclusion L w y) =
      infiniteIdeleInclusion L w y' := by
    apply Units.ext
    apply Prod.ext
    · funext p
      apply (isometry_extensionEmbedding p).injective
      rw [ideleComplexConj_infinite_coordinate]
      change star (extensionEmbedding p (Pi.mulSingle w (y : w.Completion) p)) =
        extensionEmbedding p (Pi.mulSingle w (y' : w.Completion) p)
      by_cases hp : p = w
      · subst hp
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, hy]
      · rw [Pi.mulSingle_eq_of_ne hp, Pi.mulSingle_eq_of_ne hp, map_one, star_one]
    · exact map_one (finiteAdeleEquiv (IsCMField.complexConj L).toRingEquiv)
  have h := hξ (ideleClassMap L (infiniteIdeleInclusion L w y))
  change ξ (ideleClassMap L (infiniteIdeleInclusion L w y')) =
    (ξ (ideleClassMap L (infiniteIdeleInclusion L w y)))⁻¹
  rw [← key]
  exact h

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

/-- The character of `ξ` at a place `w` above the complex place `v`, read on `K_vˣ` through the
completion map, is the character of the parameter of `ξ` at `w` transported to the coordinate
of `v`. -/
theorem infiniteComponent_completionMap {ξ : HeckeCharacter L}
    (v : {v : InfinitePlace K // v.IsComplex}) (w : InfinitePlacesAbove L v.1)
    {d : ComplexCharacterData} (hd : ξ.HasComplexPlaceParameter (complexPlaceAbove v w) d)
    (x : (InfiniteCompletion K v.1)ˣ) :
    ξ.infiniteComponent w.1
        (Units.map (NumberField.LiesOver.completionMap v.1 w.1).toMonoidHom x) =
      (normParameter v w d).character (Units.map (extensionEmbedding v.1).toMonoidHom x) := by
  refine (hd _).trans ?_
  unfold normParameter
  split_ifs with hc
  · congr 1
    apply Units.ext
    exact extensionEmbedding_completionMap_of_comp_eq v.1 w hc (x : v.1.Completion)
  · change d.character _ = d.character (complexConjugation _)
    congr 1
    apply Units.ext
    rw [coe_complexConjugation]
    exact extensionEmbedding_completionMap_of_comp_ne v.1 w hc (x : v.1.Completion)

/-- Exactly `[L : K]` places of `L` lie above a complex place of `K`. -/
theorem card_infinitePlacesAbove_eq_finrank (v : InfinitePlace K) (hv : v.IsComplex) :
    Fintype.card (InfinitePlacesAbove L v) = Module.finrank K L := by
  have hsum := infiniteLocalDegree_sum (L := L) v
  rw [Finset.sum_congr rfl fun q _ => (isUnramified_of_isComplex v hv q).finrank_eq_one v,
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at hsum
  exact hsum

/-- Concatenating the singletons of a finite family gives the list of the family. -/
theorem flatten_ofFn_singleton {α : Type*} {d : ℕ} (f : Fin d → α) :
    (List.ofFn fun i => [f i]).flatten = List.ofFn f := by
  induction d with
  | zero => simp
  | succ d ih => simp [List.ofFn_succ, ih]

/-- The Langlands sum of singletons is the list of the transported parameters. -/
theorem complexPlaceLanglandsSum_singleton (v : {v : InfinitePlace K // v.IsComplex}) {d : ℕ}
    (e : Fin d ≃ InfinitePlacesAbove L v.1)
    (a : InfinitePlacesAbove L v.1 → ComplexCharacterData) :
    complexPlaceLanglandsSum v e (fun w => [a w]) =
      List.ofFn fun i => normParameter v (e i) (a (e i)) := by
  classical
  have h : ∀ w : InfinitePlacesAbove L v.1,
      complexPlaceParameterTransport v w [a w] = [normParameter v w (a w)] := by
    intro w
    unfold complexPlaceParameterTransport normParameter
    split_ifs <;> rfl
  simp only [complexPlaceLanglandsSum, h]
  exact flatten_ofFn_singleton _

end Place

/-! ## Clozel regularity of the induced parameter -/

section Regular

variable {E E' : Type*} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
  [IsCMField E] [IsCMField E']

/-- For a Hecke character `ξ` of `E'` that is algebraic after the twist of parity
`[E' : E] - 1`, relatively regular and conjugate inverse, the Langlands sum over the places of
`E'` above a complex place `v` of `E` of the parameters of `ξ` is Clozel regular algebraic of
rank the number `d` of these places. -/
theorem isClozelRegularAlgebraic_complexPlaceLanglandsSum {ξ : HeckeCharacter E'}
    (hAlg : IsAlgebraicAfterTwist (Module.finrank E E' - 1) ξ)
    (hReg : IsRelativelyRegular E ξ) (hCI : IsConjugateInverse ξ)
    (v : {v : InfinitePlace E // v.IsComplex}) {d : ℕ} (e : Fin d ≃ InfinitePlacesAbove E' v.1)
    (dξ : InfinitePlacesAbove E' v.1 → ComplexCharacterData)
    (hdξ : ∀ w, ξ.HasComplexPlaceParameter (complexPlaceAbove v w) (dξ w)) :
    ComplexPlaceParameter.IsClozelRegularAlgebraic d
      (complexPlaceLanglandsSum v e fun w => [dξ w]) := by
  classical
  set n := Module.finrank E E' with hn
  obtain ⟨t, ht⟩ := hAlg
  -- the rank is the degree
  have hd : d = n := by
    rw [hn, ← card_infinitePlacesAbove_eq_finrank (L := E') v.1 v.2, ← Fintype.card_fin d]
    exact Fintype.card_congr e
  have hn1 : ((d : ℂ) - 1) = (((n - 1 : ℕ) : ℤ) : ℂ) := by
    have h1 : 1 ≤ n := Module.finrank_pos
    rw [hd, Int.cast_natCast, Nat.cast_sub h1, Nat.cast_one]
  -- the parameter of `ξ` at each place above `v`
  have hfacts : ∀ w : InfinitePlacesAbove E' v.1, (dξ w).exponent = 0 ∧
      ∃ p q : ℤ, (dξ w).weight = p - q ∧ p + q = ((n - 1 : ℕ) : ℤ) := by
    intro w
    have hwc : w.1.IsComplex := (complexPlaceAbove v w).2
    have hp : ∀ y : (InfiniteCompletion E' w.1)ˣ, ξ.infiniteComponent w.1 y =
        (dξ w).character (Units.map (extensionEmbedding w.1).toMonoidHom y) := hdξ w
    have hB : ∀ z : ℂˣ, ((dξ w).character z : ℂ) * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ (n - 1) =
        (z : ℂ) ^ (t w.1.embedding) *
          star (z : ℂ) ^ (t (ComplexEmbedding.conjugate w.1.embedding)) := by
      intro z
      obtain ⟨y, rfl⟩ := exists_units_map_extensionEmbedding hwc z
      have h1 := infiniteComponent_mul_norm_pow t ht w.1 y
      rw [hp y] at h1
      exact h1
    have hC : ∀ z : ℂˣ, ((dξ w).character (complexConjugation z) : ℂ) =
        ((dξ w).character z : ℂ)⁻¹ := by
      intro z
      obtain ⟨y, rfl⟩ := exists_units_map_extensionEmbedding hwc z
      obtain ⟨y', hy'⟩ := exists_units_map_extensionEmbedding hwc
        (complexConjugation (Units.map (extensionEmbedding w.1).toMonoidHom y))
      have hyc : extensionEmbedding w.1 (y' : w.1.Completion) =
          star (extensionEmbedding w.1 (y : w.1.Completion)) := by
        have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) hy'
        exact h2
      have h1 := infiniteComponent_of_coordinate_conj hCI w.1 y y' hyc
      rw [hp y', hp y, hy'] at h1
      rw [h1, Units.val_inv_eq_inv_val]
    obtain ⟨h0, hw, hs⟩ := characterData_of_twist_conj (dξ w) (n - 1) _ _ hB hC
    exact ⟨h0, _, _, hw, hs⟩
  -- the transported parameters
  set T : InfinitePlacesAbove E' v.1 → ComplexCharacterData :=
    fun w => normParameter v w (dξ w) with hT
  have hTexp : ∀ w, (T w).exponent = 0 := by
    intro w
    simp only [hT, normParameter]
    split_ifs
    · exact (hfacts w).1
    · exact (hfacts w).1
  have hTweight : ∀ w, ∃ m : ℤ, (T w).weight = ((n - 1 : ℕ) : ℤ) - 2 * m := by
    intro w
    obtain ⟨p, q, hw, hs⟩ := (hfacts w).2
    simp only [hT, normParameter]
    split_ifs
    · exact ⟨q, by rw [hw]; omega⟩
    · exact ⟨p, by change -(dξ w).weight = _; rw [hw]; omega⟩
  have hTchar : ∀ w (x : (InfiniteCompletion E v.1)ˣ),
      ξ.infiniteComponent w.1
          (Units.map (NumberField.LiesOver.completionMap v.1 w.1).toMonoidHom x) =
        (T w).character (Units.map (extensionEmbedding v.1).toMonoidHom x) :=
    fun w x => infiniteComponent_completionMap v w (hdξ w) x
  have hTinj : ∀ w w', (T w).weight = (T w').weight → w = w' := by
    intro w w' hww'
    by_contra hne
    have hne' : w.1 ≠ w'.1 := fun h => hne (Subtype.ext h)
    have := w.2
    have := w'.2
    obtain ⟨x, hx⟩ := hReg v.1 w.1 w'.1 hne'
    have hchar : (T w).character = (T w').character := by
      apply ContinuousMonoidHom.ext
      intro z
      apply Units.ext
      rw [(T w).character_eq, (T w').character_eq, hww', hTexp w, hTexp w']
    apply hx
    rw [hTchar w x, hTchar w' x, hchar]
  -- Clozel regularity
  rw [complexPlaceLanglandsSum_singleton]
  change ComplexPlaceParameter.IsClozelRegularAlgebraic d (List.ofFn fun i => T (e i))
  have hz : ∀ w, (T w).zExponent = ((T w).weight : ℂ) / 2 := by
    intro w
    rw [ComplexCharacterData.zExponent, hTexp w, zero_add]
  have hzBar : ∀ w, (T w).zBarExponent = -(((T w).weight : ℂ) / 2) := by
    intro w
    rw [ComplexCharacterData.zBarExponent, hTexp w, zero_sub]
  refine ⟨List.length_ofFn, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨m, hm⟩ := hTweight (e i)
    refine ⟨-m, m - ((n - 1 : ℕ) : ℤ), ?_, ?_⟩
    · rw [hz, hm, hn1]
      push_cast
      ring
    · rw [hzBar, hm, hn1]
      push_cast
      ring
  · rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro i j hij
    simp only [Function.comp_apply, hz] at hij
    have hw : (T (e i)).weight = (T (e j)).weight := by
      have h2 : ((T (e i)).weight : ℂ) = ((T (e j)).weight : ℂ) := by
        linear_combination 2 * hij
      exact_mod_cast h2
    exact e.injective (hTinj _ _ hw)
  · rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro i j hij
    simp only [Function.comp_apply, hzBar] at hij
    have hw : (T (e i)).weight = (T (e j)).weight := by
      have h2 : ((T (e i)).weight : ℂ) = ((T (e j)).weight : ℂ) := by
        linear_combination -2 * hij
      exact_mod_cast h2
    exact e.injective (hTinj _ _ hw)

end Regular

end Langlands.Global.Harris.InducedParameterRegularAlgebraic

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified
open InducedParameterRegularAlgebraic

/-- **Regular algebraicity from the induced parameters** (Harris 1998, Proposition 4.8, the
infinity type). Given the archimedean bridge, a cuspidal class over `E` with the complex-place
parameters of the representation induced from an algebraic, relatively regular,
conjugate-inverse `ξ` is regular algebraic. -/
theorem proposition48InducedParameterRegularAlgebraic :
    Proposition48InducedParameterRegularAlgebraicStatement.{uF} := by
  intro hBridge Q hAlg hReg hCI r c hc
  obtain ⟨S, rfl⟩ := Quotient.exists_rep c
  choose ds hds hind using hc
  have hds' : ∀ v, S.realization.HasComplexPlaceParameter v (ds v) := fun v => hds v
  obtain ⟨⟨θ, hθ, -⟩, hAct⟩ := hBridge.2.1 Q.E r S ds hds'
  refine (S.isoClass_isRegularAlgebraic_iff).mpr
    ⟨θ, (hBridge.2.2 Q.E (r + 1) ds θ hθ).mpr ?_, hAct θ hθ⟩
  intro v
  obtain ⟨d, e, dξ, hdξ, hperm⟩ := hind v
  have hlen : (ds v).length = r + 1 := (hds' v).1
  have hlen' : d = r + 1 := by
    rw [← hlen, hperm.length_eq, complexPlaceLanglandsSum_singleton, List.length_ofFn]
  rw [ComplexPlaceParameter.isClozelRegularAlgebraic_iff_of_perm hperm, ← hlen']
  exact isClozelRegularAlgebraic_complexPlaceLanglandsSum hAlg hReg hCI v e dξ hdξ

end Langlands.Global.Harris
