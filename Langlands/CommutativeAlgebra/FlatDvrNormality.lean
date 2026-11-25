import Langlands.MathlibBase

/-! # Normality criteria for algebras flat over a discrete valuation ring -/

noncomputable section

open Polynomial

namespace Langlands.CommutativeAlgebra.FlatDvrNormality

section Integral

variable {B L : Type*} [CommRing B] [CommRing L] [Algebra B L]

/-- If `x` is integral over `B` and `π * x = b` with `b ∈ B`, then `b ∈ π B`,
provided `B / π B` is reduced and `B → L` is injective. -/
theorem mem_span_of_isIntegral_mul {π b : B} {x : L}
    (hinj : Function.Injective (algebraMap B L)) (hred : IsReduced (B ⧸ Ideal.span {π}))
    (hx : IsIntegral B x) (hb : algebraMap B L π * x = algebraMap B L b) :
    b ∈ Ideal.span {π} := by
  obtain ⟨p, hpm, hp⟩ := hx
  have h1 : aeval (algebraMap B L π * x) (p.scaleRoots π) = 0 :=
    scaleRoots_aeval_eq_zero (by rwa [aeval_def])
  rw [hb, aeval_algebraMap_apply] at h1
  have h2 : aeval b (p.scaleRoots π) = 0 := hinj (by rw [h1, map_zero])
  set mk := Ideal.Quotient.mk (Ideal.span {π})
  have hq : (p.scaleRoots π).map mk = X ^ p.natDegree := by
    ext i
    simp only [coeff_map, coeff_scaleRoots, coeff_X_pow]
    rcases lt_trichotomy i p.natDegree with h | rfl | h
    · simp only [h.ne, ↓reduceIte]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) _ (Nat.sub_pos_of_lt h))
    · simp only [↓reduceIte]
      rw [← leadingCoeff, hpm.leadingCoeff, Nat.sub_self, pow_zero, mul_one,
        map_one]
    · simp only [h.ne', ↓reduceIte]
      rw [coeff_eq_zero_of_natDegree_lt h, zero_mul, map_zero]
  have h3 : eval (mk b) ((p.scaleRoots π).map mk) = 0 := by
    rw [eval_map, eval₂_hom, ← coe_aeval_eq_eval, h2, map_zero]
  rw [hq, eval_pow, eval_X] at h3
  have hnil : IsNilpotent (mk b) := ⟨_, h3⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp hnil.eq_zero

/-- Generic induction: if every integral `y` with `π y ∈ B` has `π y ∈ π B`, and `π` is
cancellable in `L`, then every integral `x` with `π^n x ∈ B` lies in `B`. -/
theorem mem_range_of_pow_mul_of_key {π : B} (hπ : IsLeftRegular (algebraMap B L π))
    (hkey : ∀ y : L, IsIntegral B y → ∀ b : B, algebraMap B L π * y = algebraMap B L b →
      b ∈ Ideal.span {π}) :
    ∀ (n : ℕ) {x : L}, IsIntegral B x → algebraMap B L π ^ n * x ∈ (algebraMap B L).range →
      x ∈ (algebraMap B L).range := by
  intro n
  induction n with
  | zero => intro x _ h; simpa using h
  | succ n ih =>
    intro x hx h
    obtain ⟨b, hb⟩ := h
    have hy : IsIntegral B (algebraMap B L π ^ n * x) :=
      ((isIntegral_algebraMap (x := π)).pow n).mul hx
    have hmem := hkey _ hy b (by rw [hb, pow_succ]; ring)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ih hx ⟨c, hπ ?_⟩
    simp only [map_mul] at hb
    change algebraMap B L π * algebraMap B L c = algebraMap B L π * (algebraMap B L π ^ n * x)
    rw [mul_comm, hb, pow_succ]; ring

/-- If `x` is integral over `B`, `π^n x ∈ B`, `B / π B` is reduced, `B → L` is injective and
`π` is cancellable in `L`, then `x ∈ B`. -/
theorem mem_range_of_isIntegral_of_pow_mul {π : B} (hinj : Function.Injective (algebraMap B L))
    (hπ : IsLeftRegular (algebraMap B L π)) (hred : IsReduced (B ⧸ Ideal.span {π}))
    (n : ℕ) {x : L} (hx : IsIntegral B x)
    (h : algebraMap B L π ^ n * x ∈ (algebraMap B L).range) : x ∈ (algebraMap B L).range :=
  mem_range_of_pow_mul_of_key hπ
    (fun _ hy _ hb => mem_span_of_isIntegral_mul hinj hred hy hb) n hx h

end Integral

section Local

variable {B : Type*} [CommRing B]

/-- A Noetherian local ring with a non-zero-divisor `π` in its maximal ideal and reduced
quotient `B / π B` is reduced (Krull intersection theorem). -/
theorem isReduced_of_quotient [IsLocalRing B] [IsNoetherianRing B] {π : B}
    (hπm : π ∈ IsLocalRing.maximalIdeal B) (hπ : π ∈ nonZeroDivisors B)
    (hred : IsReduced (B ⧸ Ideal.span {π})) : IsReduced B := by
  have key : ∀ n : ℕ, ∀ b : B, IsNilpotent b → b ∈ Ideal.span {π} ^ n := by
    intro n
    induction n with
    | zero => intro b _; simp
    | succ n ih =>
      intro b hb
      have hb' : b ∈ Ideal.span {π} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        exact (hb.map (Ideal.Quotient.mk (Ideal.span {π}))).eq_zero
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb'
      have hc : IsNilpotent c := by
        obtain ⟨k, hk⟩ := hb
        refine ⟨k, ?_⟩
        rw [mul_pow] at hk
        exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hπ k)).mp hk
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih c hc) (Ideal.mem_span_singleton_self π)
  refine ⟨fun b hb => ?_⟩
  have hmem : b ∈ ⨅ n : ℕ, Ideal.span {π} ^ n := Ideal.mem_iInf.mpr fun n => key n b hb
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ ?_] at hmem
  · exact (Submodule.mem_bot B).mp hmem
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    exact (IsLocalRing.mem_maximalIdeal _).mp hπm h

/-- If the localization at a prime `Q` is a domain, then at most one minimal prime of `B` is
contained in `Q`. -/
theorem eq_of_minimalPrimes_le {Q P₁ P₂ : Ideal B} [Q.IsPrime]
    [IsDomain (Localization.AtPrime Q)] (h₁ : P₁ ∈ minimalPrimes B) (h₂ : P₂ ∈ minimalPrimes B)
    (hle₁ : P₁ ≤ Q) (hle₂ : P₂ ≤ Q) : P₁ = P₂ := by
  let P₀ : Ideal B := (⊥ : Ideal (Localization.AtPrime Q)).comap
    (algebraMap B (Localization.AtPrime Q))
  have hP₀ : P₀.IsPrime := Ideal.comap_isPrime _ _
  have hle : ∀ P : Ideal B, P.IsPrime → P ≤ Q → P₀ ≤ P := by
    intro P hP hPQ x hx
    have hx0 : algebraMap B (Localization.AtPrime Q) x = 0 :=
      Ideal.mem_bot.mp (Ideal.mem_comap.mp hx)
    obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ x).mp hx0
    have hsP : s ∉ P := fun h => hs (hPQ h)
    exact (hP.mem_or_mem (hsx ▸ P.zero_mem)).resolve_left hsP
  have h₁' : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) P₁ := h₁
  have h₂' : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) P₂ := h₂
  have e₁ := h₁'.eq_of_le ⟨hP₀, bot_le⟩ (hle P₁ h₁'.1.1 hle₁)
  have e₂ := h₂'.eq_of_le ⟨hP₀, bot_le⟩ (hle P₂ h₂'.1.1 hle₂)
  exact e₁.symm.trans e₂

/-- Local criterion for being a domain: a Noetherian local ring with a non-zero-divisor `π`
in the maximal ideal, reduced quotient `B / π B`, and domain localizations at all primes not
containing `π`, is a domain. -/
theorem isDomain_of_quotient [IsLocalRing B] [IsNoetherianRing B] {π : B}
    (hπm : π ∈ IsLocalRing.maximalIdeal B) (hπ : π ∈ nonZeroDivisors B)
    (hred : IsReduced (B ⧸ Ideal.span {π}))
    (hgen : ∀ (Q : Ideal B) [Q.IsPrime], π ∉ Q → IsDomain (Localization.AtPrime Q)) :
    IsDomain B := by
  have : IsReduced B := isReduced_of_quotient hπm hπ hred
  have hfin := minimalPrimes.finite_of_isNoetherianRing B
  have hπP : ∀ P ∈ minimalPrimes B, π ∉ P := fun P hP hπP =>
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hπP hπ
  have hsub : (minimalPrimes B).Subsingleton := by
    intro P₁ hP₁ P₂ hP₂
    by_contra hne
    have := hP₁.1.1
    let s : Finset (Ideal B) := hfin.toFinset.erase P₁
    have hP₂s : P₂ ∈ s := Finset.mem_erase.mpr ⟨Ne.symm hne, hfin.mem_toFinset.mpr hP₂⟩
    let J : Ideal B := s.inf id
    have hJ : ∀ P ∈ s, J ≤ P := fun P hP => Finset.inf_le (f := id) hP
    have hs_min : ∀ P ∈ s, P ∈ minimalPrimes B := fun P hP =>
      hfin.mem_toFinset.mp (Finset.mem_of_mem_erase hP)
    -- some power of `π` lies in `P₁ ⊔ J`
    have hex : ∃ n : ℕ, π ^ n ∈ P₁ ⊔ J := by
      by_contra hno'
      have hno := not_exists.mp hno'
      have hdisj : Disjoint ((P₁ ⊔ J : Ideal B) : Set B) (Submonoid.powers π) := by
        rw [Set.disjoint_left]
        rintro x hx ⟨n, rfl⟩
        exact hno n hx
      obtain ⟨Q, hQ, hle, hQdisj⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
      have hπQ : π ∉ Q := fun h =>
        Set.disjoint_left.mp hQdisj h (Submonoid.mem_powers π)
      have := hgen Q hπQ
      obtain ⟨P, hPs, hPQ⟩ := (hQ.inf_le' (s := s) (f := id)).mp (le_sup_right.trans hle)
      have := eq_of_minimalPrimes_le (Q := Q) hP₁ (hs_min P hPs) (le_sup_left.trans hle) hPQ
      exact (Finset.mem_erase.mp hPs).1 this.symm
    classical
    let n := Nat.find hex
    have hn : π ^ n ∈ P₁ ⊔ J := Nat.find_spec hex
    have hmin : ∀ k < n, π ^ k ∉ P₁ ⊔ J := fun k hk => Nat.find_min hex hk
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at hn
      have hm : P₁ ⊔ J ≤ IsLocalRing.maximalIdeal B :=
        sup_le (IsLocalRing.le_maximalIdeal hP₁.1.1.ne_top)
          ((hJ P₂ hP₂s).trans (IsLocalRing.le_maximalIdeal hP₂.1.1.ne_top))
      exact (IsLocalRing.mem_maximalIdeal _).mp (hm hn) isUnit_one
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨a₁, ha₁, a₂, ha₂, hsum⟩ := Submodule.mem_sup.mp hn
      -- `a₁ a₂ = 0`
      have hprod : a₁ * a₂ = 0 := by
        have : a₁ * a₂ ∈ nilradical B := by
          rw [nilradical, ← Ideal.sInf_minimalPrimes]
          refine Submodule.mem_sInf.mpr fun P hP => ?_
          by_cases hPP : P = P₁
          · subst hPP; exact Ideal.mul_mem_right a₂ P ha₁
          · have hPs : P ∈ s := Finset.mem_erase.mpr ⟨hPP, hfin.mem_toFinset.mpr hP⟩
            exact Ideal.mul_mem_left P a₁ (hJ P hPs ha₂)
        rw [nilradical_eq_zero] at this
        exact this
      have hsq : ∀ a b : B, a + b = π ^ n → a * b = 0 → a ∈ Ideal.span {π} := by
        intro a b hab habz
        have ha2 : a ^ 2 = π ^ n * a := by
          linear_combination a * hab - habz
        have hmem : a ^ 2 ∈ Ideal.span {π} := by
          rw [ha2, hk, pow_succ]
          exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self π))
        rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem ⊢
        exact (IsNilpotent.eq_zero ⟨2, by rw [← map_pow]; exact hmem⟩)
      obtain ⟨c₁, rfl⟩ := Ideal.mem_span_singleton'.mp (hsq a₁ a₂ hsum hprod)
      obtain ⟨c₂, rfl⟩ := Ideal.mem_span_singleton'.mp
        (hsq a₂ (c₁ * π) (by rw [add_comm]; exact hsum) (by rw [mul_comm]; exact hprod))
      have hc₁ : c₁ ∈ P₁ := (hP₁.1.1.mem_or_mem ha₁).resolve_right (hπP P₁ hP₁)
      have hc₂ : c₂ ∈ J := by
        refine Submodule.mem_finsetInf.mpr fun P hPs => ?_
        exact ((hs_min P hPs).1.1.mem_or_mem (hJ P hPs ha₂)).resolve_right (hπP P (hs_min P hPs))
      have hk' : π ^ k = c₁ + c₂ := by
        have h1 : π ^ k * π = (c₁ + c₂) * π := by rw [← pow_succ, ← hk, ← hsum]; ring
        exact (mul_cancel_right_mem_nonZeroDivisors hπ).mp h1
      exact hmin k (by omega) (hk' ▸ Submodule.add_mem_sup hc₁ hc₂)
  -- a unique minimal prime in a reduced ring is zero
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes (R := B) (I := ⊥) bot_ne_top
  have hPeq : minimalPrimes B = {P} := hsub.eq_singleton_of_mem hP
  have hbot : (⊥ : Ideal B) = P := by
    have h := Ideal.sInf_minimalPrimes (I := (⊥ : Ideal B))
    have h' : sInf (minimalPrimes B) = P := by rw [hPeq, sInf_singleton]
    have hrad : (⊥ : Ideal B).radical = ⊥ := by
      change nilradical B = ⊥
      rw [nilradical_eq_zero]; rfl
    calc (⊥ : Ideal B) = (⊥ : Ideal B).radical := hrad.symm
      _ = sInf (⊥ : Ideal B).minimalPrimes := h.symm
      _ = P := h'
  have : (⊥ : Ideal B).IsPrime := hbot ▸ hP.1.1
  exact IsDomain.of_bot_isPrime B

/-- A domain `B` with `π ≠ 0`, reduced quotient `B / π B`, and integrally closed localizations
at all primes not containing `π`, is integrally closed. -/
theorem isIntegrallyClosed_of_quotient [IsDomain B] {π : B} (hπ0 : π ≠ 0)
    (hred : IsReduced (B ⧸ Ideal.span {π}))
    (hgen : ∀ (Q : Ideal B) [Q.IsPrime], π ∉ Q → IsIntegrallyClosed (Localization.AtPrime Q)) :
    IsIntegrallyClosed B := by
  let K := FractionRing B
  rw [isIntegrallyClosed_iff K]
  intro x hx
  have hloc : ∀ (Q : Ideal B) [Q.IsPrime], π ∉ Q →
      ∃ s ∉ Q, algebraMap B K s * x ∈ (algebraMap B K).range := by
    intro Q _ hπQ
    let S := Localization.subalgebra.ofField K Q.primeCompl Q.primeCompl_le_nonZeroDivisors
    have hS : IsIntegrallyClosed S := (hgen Q hπQ).of_equiv
      (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) S).toRingEquiv
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp hS hx.tower_top
    have hy2 : (y : K) ∈ {z : K | ∃ (a s : B) (_ : s ∈ Q.primeCompl),
        z = algebraMap B K a * (algebraMap B K s)⁻¹} := y.2
    obtain ⟨a, s, hs, hxa⟩ := hy2
    refine ⟨s, hs, a, ?_⟩
    have hs0 : algebraMap B K s ≠ 0 := by
      intro h
      apply hs
      rw [(IsFractionRing.injective B K).eq_iff.mp (h.trans (map_zero _).symm)]
      exact Q.zero_mem
    have hyx : (y : K) = x := hy
    rw [← hyx, hxa, mul_comm (algebraMap B K a), ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
  let D : Ideal B :=
    { carrier := {b | algebraMap B K b * x ∈ (algebraMap B K).range}
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨d, hd⟩
        exact ⟨c + d, by rw [map_add, map_add, add_mul, hc, hd]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c b ⟨d, hd⟩
        exact ⟨c * d, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hd]⟩ }
  have hex : ∃ n : ℕ, π ^ n ∈ D := by
    by_contra hno'
    have hno := not_exists.mp hno'
    have hdisj : Disjoint ((D : Set B)) (Submonoid.powers π) := by
      rw [Set.disjoint_left]
      rintro y hy ⟨n, rfl⟩
      exact hno n hy
    obtain ⟨Q, hQ, hle, hQdisj⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
    have hπQ : π ∉ Q := fun h => Set.disjoint_left.mp hQdisj h (Submonoid.mem_powers π)
    obtain ⟨s, hsQ, hs⟩ := hloc Q hπQ
    exact hsQ (hle hs)
  obtain ⟨n, hn⟩ := hex
  have hπK : algebraMap B K π ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B K), (IsFractionRing.injective B K).eq_iff]
    exact hπ0
  obtain ⟨y, hy⟩ := mem_range_of_isIntegral_of_pow_mul (IsFractionRing.injective B K)
    (IsRegular.of_ne_zero hπK).left hred n hx
    (by obtain ⟨z, hz⟩ := hn; exact ⟨z, by rw [hz, map_pow]⟩)
  exact ⟨y, hy⟩

/-- Local normality criterion over a uniformizer-like element: a Noetherian local ring `B`
with a non-zero-divisor `π`, reduced `B / π B`, and normal-domain localizations at all primes
not containing `π`, is an integrally closed domain. -/
theorem isDomain_and_isIntegrallyClosed_of_quotient [IsLocalRing B] [IsNoetherianRing B]
    {π : B} (hπ : π ∈ nonZeroDivisors B) (hred : IsReduced (B ⧸ Ideal.span {π}))
    (hgen : ∀ (Q : Ideal B) [Q.IsPrime], π ∉ Q →
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    IsDomain B ∧ IsIntegrallyClosed B := by
  by_cases hπm : π ∈ IsLocalRing.maximalIdeal B
  · have hdom : IsDomain B := isDomain_of_quotient hπm hπ hred fun Q _ hQ => (hgen Q hQ).1
    exact ⟨hdom, isIntegrallyClosed_of_quotient (nonZeroDivisors.ne_zero hπ) hred
      fun Q _ hQ => (hgen Q hQ).2⟩
  · obtain ⟨h1, h2⟩ := hgen (IsLocalRing.maximalIdeal B) hπm
    let e : B ≃ₐ[B] Localization.AtPrime (IsLocalRing.maximalIdeal B) :=
      IsLocalization.atUnits B (IsLocalRing.maximalIdeal B).primeCompl
        (fun x hx => IsLocalRing.notMem_maximalIdeal.mp hx)
    exact ⟨e.toMulEquiv.isDomain, h2.of_equiv e.symm.toRingEquiv⟩

end Local

section Global

variable {C : Type*} [CommRing C]

/-- If `C / π C` is reduced, so is `C_p / π C_p` for every prime `p`. -/
theorem isReduced_localization_quotient {π : C} (hred : IsReduced (C ⧸ Ideal.span {π}))
    (p : Ideal C) [p.IsPrime] :
    IsReduced (Localization.AtPrime p ⧸
      Ideal.span {algebraMap C (Localization.AtPrime p) π}) := by
  refine ⟨fun z hz => ?_⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨k, hk⟩ := hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hk
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  obtain ⟨⟨d, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl w
  rw [← IsLocalization.mk'_pow, ← IsLocalization.mk'_one (M := p.primeCompl)
    (Localization.AtPrime p) π, ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq,
    IsLocalization.eq_iff_exists p.primeCompl] at hw
  obtain ⟨⟨u, hu⟩, hu'⟩ := hw
  simp only [SubmonoidClass.coe_pow, mul_one] at hu'
  -- `(u t c)^(k+1) ∈ π C`
  have hmem : (u * t * c) ^ (k + 1) ∈ Ideal.span {π} := by
    have : (u * t * c) ^ (k + 1) = (u * (t : C)) ^ k * (u * (s ^ k * (d * π)) * c) := by
      linear_combination (-(u * (t : C)) ^ k * c) * hu'
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self π)))))
  have hmem' : u * t * c ∈ Ideal.span {π} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem ⊢
    exact IsNilpotent.eq_zero ⟨k + 1, by rw [← map_pow]; exact hmem⟩
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem'
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  have hut : u * t ∈ p.primeCompl := p.primeCompl.mul_mem hu t.2
  refine ⟨IsLocalization.mk' (Localization.AtPrime p) e (⟨u * t, hut⟩ * s), ?_⟩
  rw [← IsLocalization.mk'_one (M := p.primeCompl) (Localization.AtPrime p) π,
    ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp only [Submonoid.coe_mul, mul_one]
  congr 1
  rw [he]; ring

/-- Affine normality criterion: for a Noetherian ring `C` with a non-zero-divisor `π` such that
`C / π C` is reduced and the localizations at primes not containing `π` are integrally closed
domains, every localization at a prime is an integrally closed domain. -/
theorem isDomain_and_isIntegrallyClosed_localization [IsNoetherianRing C] {π : C}
    (hπ : π ∈ nonZeroDivisors C) (hred : IsReduced (C ⧸ Ideal.span {π}))
    (hgen : ∀ (q : Ideal C) [q.IsPrime], π ∉ q →
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal C) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  have hπ' : algebraMap C (Localization.AtPrime p) π ∈ nonZeroDivisors (Localization.AtPrime p) :=
    IsLocalization.map_nonZeroDivisors_le p.primeCompl (Localization.AtPrime p)
      (Submonoid.mem_map_of_mem _ hπ)
  refine isDomain_and_isIntegrallyClosed_of_quotient hπ'
    (isReduced_localization_quotient hred p) fun Q _ hQ => ?_
  let q : Ideal C := Q.comap (algebraMap C (Localization.AtPrime p))
  have hq : π ∉ q := hQ
  obtain ⟨h1, h2⟩ := hgen q hq
  let e : Localization.AtPrime q ≃ₐ[C] Localization.AtPrime Q :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact ⟨e.symm.toMulEquiv.isDomain, h2.of_equiv e.toRingEquiv⟩

/-- A ring with a non-zero-divisor `π` whose localizations at maximal ideals are integrally
closed domains is integrally closed in `C[1/π]`. -/
theorem mem_range_of_isIntegral_of_normal {L : Type*} [CommRing L] [Algebra C L]
    (π : C) [IsLocalization.Away π L] (hπ : π ∈ nonZeroDivisors C)
    (hnorm : ∀ (m : Ideal C) [m.IsMaximal],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m))
    {x : L} (hx : IsIntegral C x) : x ∈ (algebraMap C L).range := by
  obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj π x
  refine mem_range_of_pow_mul_of_key (IsLocalization.Away.algebraMap_isUnit π).isRegular.left
    ?_ n hx ⟨a, by rw [mul_comm]; exact hn.symm⟩
  intro y hy b hb
  let D : Ideal C := Submodule.comap (LinearMap.mulRight C b) (Ideal.span {π})
  have hD : D = ⊤ := by
    by_contra hD
    obtain ⟨m, hm, hDm⟩ := Ideal.exists_le_maximal D hD
    obtain ⟨hdom, hic⟩ := hnorm m
    let Bm := Localization.AtPrime m
    let Km := FractionRing Bm
    let g : C →+* Km := (algebraMap Bm Km).comp (algebraMap C Bm)
    have hπm : algebraMap C Bm π ≠ 0 := by
      intro h
      obtain ⟨⟨s, hs⟩, hs'⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl Bm π).mp h
      have h0 : s = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff hπ).mp hs'
      exact hs (by rw [h0]; exact m.zero_mem)
    have hg : IsUnit (g π) := by
      refine isUnit_iff_ne_zero.mpr ?_
      rw [RingHom.comp_apply, Ne, ← map_zero (algebraMap Bm Km),
        (IsFractionRing.injective Bm Km).eq_iff]
      exact hπm
    let φ : L →+* Km := IsLocalization.Away.lift π hg
    have hφ : φ.comp (algebraMap C L) = g := IsLocalization.Away.lift_comp π hg
    have hφa : ∀ c : C, φ (algebraMap C L c) = g c := fun c => by rw [← hφ]; rfl
    obtain ⟨P, hPm, hP⟩ := hy
    have hz : IsIntegral Bm (φ y) := by
      refine ⟨P.map (algebraMap C Bm), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      change Polynomial.eval₂ g (φ y) P = 0
      rw [← hφ, ← Polynomial.hom_eval₂, hP, map_zero]
    obtain ⟨w, hw⟩ := (isIntegrallyClosed_iff Km).mp hic hz
    have hbw : algebraMap C Bm π * w = algebraMap C Bm b := by
      apply IsFractionRing.injective Bm Km
      rw [map_mul, hw]
      have := congrArg φ hb
      rw [map_mul, hφa, hφa] at this
      exact this
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl w
    rw [← IsLocalization.mk'_one (M := m.primeCompl) Bm π, ← IsLocalization.mk'_mul,
      ← IsLocalization.mk'_one (M := m.primeCompl) Bm b, IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists m.primeCompl] at hbw
    obtain ⟨⟨t, ht⟩, ht'⟩ := hbw
    simp only [Submonoid.coe_one, one_mul] at ht'
    have hts : t * s ∈ D := by
      change t * s * b ∈ Ideal.span {π}
      rw [Ideal.mem_span_singleton']
      exact ⟨t * c, by linear_combination ht'⟩
    exact (m.primeCompl.mul_mem ht s.2) (hDm hts)
  have h1 : (1 : C) ∈ D := hD ▸ Submodule.mem_top
  change 1 * b ∈ Ideal.span {π} at h1
  rwa [one_mul] at h1

end Global

end Langlands.CommutativeAlgebra.FlatDvrNormality
