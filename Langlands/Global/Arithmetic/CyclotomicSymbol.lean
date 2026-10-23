import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Explicit cyclotomic symbols over `ℚ`

For a modulus `m` and a prime `p`, the symbol `localSymbol p m : ℚ_pˣ → (ℤ/m)ˣ` sends
`a = p^μ u` (with `u ∈ ℤ_pˣ`) to the residue class congruent to `u⁻¹` modulo the `p`-part
of `m` and to `p^μ` modulo the prime-to-`p` part. Together with the sign at the real place
they satisfy the product formula on `ℚˣ`.
-/

noncomputable section

namespace Langlands.Global.CyclotomicSymbol

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

theorem norm_mul_zpow_neg_valuation (a : ℚ_[p]ˣ) :
    ‖(a : ℚ_[p]) * (p : ℚ_[p]) ^ (-(a : ℚ_[p]).valuation)‖ = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [norm_mul, norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation a.ne_zero, inv_zpow',
    neg_neg, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero]

/-- The unit part `a · p^{-v(a)} ∈ ℤ_pˣ` of `a ∈ ℚ_pˣ`. -/
def unitPart (a : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_mul_zpow_neg_valuation p a)

theorem coe_unitPart (a : ℚ_[p]ˣ) :
    ((unitPart p a : ℤ_[p]) : ℚ_[p]) = a * (p : ℚ_[p]) ^ (-(a : ℚ_[p]).valuation) :=
  rfl

/-- The valuation as a homomorphism on units. -/
def valuationHom : ℚ_[p]ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (a : ℚ_[p]).valuation
  map_one' := by rw [Units.val_one, Padic.valuation_one, ofAdd_zero]
  map_mul' a b := by
    rw [Units.val_mul, Padic.valuation_mul a.ne_zero b.ne_zero, ofAdd_add]

/-- The unit part as a homomorphism. -/
def unitPartHom : ℚ_[p]ˣ →* ℤ_[p]ˣ where
  toFun := unitPart p
  map_one' := by
    apply Units.ext
    apply PadicInt.ext
    rw [coe_unitPart, Units.val_one, Padic.valuation_one, neg_zero, zpow_zero, mul_one]
    rfl
  map_mul' a b := by
    apply Units.ext
    apply PadicInt.ext
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [Units.val_mul, PadicInt.coe_mul, coe_unitPart, coe_unitPart, coe_unitPart, Units.val_mul,
      Padic.valuation_mul a.ne_zero b.ne_zero, neg_add, zpow_add₀ hp0]
    ring

theorem unitPartHom_apply (a : ℚ_[p]ˣ) : unitPartHom p a = unitPart p a := rfl

theorem valuationHom_apply (a : ℚ_[p]ˣ) :
    valuationHom p a = Multiplicative.ofAdd (a : ℚ_[p]).valuation := rfl

end Padic

section Modulus

variable (m : ℕ) [NeZero m]

/-- The `q`-part of `m` divides `m`; reduction of `(ℤ/m)ˣ` modulo the `q`-part. -/
def reduction (q : ℕ) : (ZMod m)ˣ →* (ZMod (q ^ m.factorization q))ˣ :=
  Units.map (ZMod.castHom (Nat.ordProj_dvd m q) (ZMod (q ^ m.factorization q))).toMonoidHom

omit [NeZero m] in
theorem val_reduction (q : ℕ) (x : (ZMod m)ˣ) :
    ((reduction m q x : ZMod (q ^ m.factorization q))) =
      ZMod.castHom (Nat.ordProj_dvd m q) _ (x : ZMod m) := rfl

/-- A unit modulo `m` is `1` when it is `1` modulo every prime-power part of `m`. -/
theorem eq_one_of_reduction (x : (ZMod m)ˣ) (h : ∀ q : ℕ, q.Prime → reduction m q x = 1) :
    x = 1 := by
  set z : ZMod m := (x : ZMod m) - 1 with hz_def
  suffices hz : z = 0 from Units.ext (sub_eq_zero.1 hz)
  have hdvd : ∀ q : ℕ, q.Prime → q ^ m.factorization q ∣ z.val := by
    intro q hq
    have h1 := congrArg Units.val (h q hq)
    simp only [val_reduction, Units.val_one] at h1
    have h2 : ZMod.castHom (Nat.ordProj_dvd m q) (ZMod (q ^ m.factorization q)) z = 0 := by
      rw [hz_def, map_sub, map_one, h1, sub_self]
    rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff] at h2
    exact h2
  by_contra hne
  have hv : z.val ≠ 0 := (ZMod.val_ne_zero z).2 hne
  have hm : m ∣ z.val := (Nat.factorization_prime_le_iff_dvd (NeZero.ne m) hv).1 fun q hq =>
    (hq.pow_dvd_iff_le_factorization hv).1 (hdvd q hq)
  exact hv (Nat.eq_zero_of_dvd_of_lt hm (ZMod.val_lt z))

variable (p : ℕ) [hp : Fact p.Prime]

theorem coprime_ordProj_ordCompl :
    Nat.Coprime (p ^ m.factorization p) (m / p ^ m.factorization p) :=
  Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp.out (NeZero.ne m))

/-- The Chinese remainder decomposition of `(ℤ/m)ˣ` into the `p`-part and the prime-to-`p`
part. -/
def crtUnits :
    (ZMod (p ^ m.factorization p))ˣ × (ZMod (m / p ^ m.factorization p))ˣ ≃* (ZMod m)ˣ :=
  MulEquiv.prodUnits.symm.trans
    ((Units.mapEquiv (ZMod.chineseRemainder (coprime_ordProj_ordCompl m p)).symm.toMulEquiv).trans
      (Units.mapEquiv (ZMod.ringEquivCongr (Nat.ordProj_mul_ordCompl_eq_self m p)).toMulEquiv))

theorem coe_crtUnits (x : (ZMod (p ^ m.factorization p))ˣ)
    (y : (ZMod (m / p ^ m.factorization p))ˣ) :
    ((crtUnits m p (x, y) : (ZMod m)ˣ) : ZMod m) =
      ZMod.ringEquivCongr (Nat.ordProj_mul_ordCompl_eq_self m p)
        ((ZMod.chineseRemainder (coprime_ordProj_ordCompl m p)).symm ((x : ZMod _), (y : ZMod _))) :=
  rfl

/-- The class of `p` modulo the prime-to-`p` part of `m`. -/
def primeUnit : (ZMod (m / p ^ m.factorization p))ˣ :=
  ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp.out (NeZero.ne m))

/-- The explicit local cyclotomic symbol `ℚ_pˣ → (ℤ/m)ˣ`: `p^μ u ↦ (u⁻¹, p^μ)` in the Chinese
remainder decomposition. -/
def localSymbol : ℚ_[p]ˣ →* (ZMod m)ˣ :=
  (crtUnits m p).toMonoidHom.comp
    (MonoidHom.prod
      ((Units.map (PadicInt.toZModPow (m.factorization p)).toMonoidHom).comp
        (unitPartHom p)⁻¹)
      ((zpowersHom _ (primeUnit m p)).comp (valuationHom p)))

theorem localSymbol_apply (a : ℚ_[p]ˣ) :
    localSymbol m p a = crtUnits m p
      (Units.map (PadicInt.toZModPow (m.factorization p)).toMonoidHom (unitPart p a)⁻¹,
        primeUnit m p ^ (a : ℚ_[p]).valuation) := rfl

theorem castHom_crtUnits_fst (x : (ZMod (p ^ m.factorization p))ˣ)
    (y : (ZMod (m / p ^ m.factorization p))ˣ) :
    ZMod.castHom (Nat.ordProj_dvd m p) (ZMod (p ^ m.factorization p)) (crtUnits m p (x, y)) =
      x := by
  have key : (ZMod.castHom (Nat.ordProj_dvd m p) (ZMod (p ^ m.factorization p))).comp
      (ZMod.ringEquivCongr (Nat.ordProj_mul_ordCompl_eq_self m p)).toRingHom =
      (RingHom.fst _ _).comp (ZMod.chineseRemainder (coprime_ordProj_ordCompl m p)).toRingHom :=
    RingHom.ext_zmod _ _
  have h := congrArg (fun f => f ((ZMod.chineseRemainder (coprime_ordProj_ordCompl m p)).symm
    ((x : ZMod _), (y : ZMod _)))) key
  rw [coe_crtUnits]
  simpa using h

theorem castHom_crtUnits_snd {d : ℕ} (hd : d ∣ m / p ^ m.factorization p) (hdm : d ∣ m)
    (x : (ZMod (p ^ m.factorization p))ˣ) (y : (ZMod (m / p ^ m.factorization p))ˣ) :
    ZMod.castHom hdm (ZMod d) (crtUnits m p (x, y)) = ZMod.castHom hd (ZMod d) y := by
  have key : (ZMod.castHom hdm (ZMod d)).comp
      (ZMod.ringEquivCongr (Nat.ordProj_mul_ordCompl_eq_self m p)).toRingHom =
      ((ZMod.castHom hd (ZMod d)).comp (RingHom.snd _ _)).comp
        (ZMod.chineseRemainder (coprime_ordProj_ordCompl m p)).toRingHom :=
    RingHom.ext_zmod _ _
  have h := congrArg (fun f => f ((ZMod.chineseRemainder (coprime_ordProj_ordCompl m p)).symm
    ((x : ZMod _), (y : ZMod _)))) key
  rw [coe_crtUnits]
  simpa using h

/-- Modulo the `p`-part of `m`, the symbol of `a` is the inverse of the unit part of `a`. -/
theorem reduction_localSymbol_self (a : ℚ_[p]ˣ) :
    reduction m p (localSymbol m p a) =
      (Units.map (PadicInt.toZModPow (m.factorization p)).toMonoidHom (unitPart p a))⁻¹ := by
  apply Units.ext
  rw [val_reduction, localSymbol_apply, castHom_crtUnits_fst, map_inv]

omit [NeZero m] in
theorem ordProj_dvd_ordCompl {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    q ^ m.factorization q ∣ m / p ^ m.factorization p := by
  have hcop : Nat.Coprime (q ^ m.factorization q) (p ^ m.factorization p) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp.out).2 hqp)
  refine hcop.dvd_of_dvd_mul_left ?_
  rw [Nat.ordProj_mul_ordCompl_eq_self]
  exact Nat.ordProj_dvd m q

/-- Modulo the `q`-part of `m` for a prime `q ≠ p`, the symbol of `a` is `p ^ v(a)`. -/
theorem reduction_localSymbol_of_ne {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (a : ℚ_[p]ˣ) :
    reduction m q (localSymbol m p a) =
      ZMod.unitOfCoprime p (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out hq).2
        hqp.symm)) ^ (a : ℚ_[p]).valuation := by
  have hd := ordProj_dvd_ordCompl m p hq hqp
  have hmap : Units.map (ZMod.castHom hd (ZMod (q ^ m.factorization q))).toMonoidHom
      (primeUnit m p) = ZMod.unitOfCoprime p (Nat.Coprime.pow_right _
        ((Nat.coprime_primes hp.out hq).2 hqp.symm)) := by
    apply Units.ext
    simp [primeUnit]
  apply Units.ext
  rw [val_reduction, localSymbol_apply, castHom_crtUnits_snd m p hd, ← hmap, ← map_zpow]
  rfl

omit [NeZero m] in
theorem units_eq_of_eq_one {n : ℕ} (hn : n = 1) (x y : (ZMod n)ˣ) : x = y := by
  subst hn
  exact Subsingleton.elim x y

omit [Fact p.Prime] in
theorem eq_of_reduction (x y : (ZMod m)ˣ) (h : ∀ q : ℕ, q.Prime → reduction m q x = reduction m q y) :
    x = y := by
  rw [← div_eq_one]
  exact eq_one_of_reduction m _ fun q hq => by rw [map_div, h q hq, div_self']

/-- For `p ∤ m` the symbol is unramified: `a ↦ p ^ v(a)`. -/
theorem localSymbol_of_not_dvd (hpm : ¬p ∣ m) (a : ℚ_[p]ˣ) :
    localSymbol m p a =
      ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm) ^
        (a : ℚ_[p]).valuation := by
  refine eq_of_reduction m _ _ fun q hq => ?_
  by_cases hqp : q = p
  · subst hqp
    exact units_eq_of_eq_one (by rw [Nat.factorization_eq_zero_of_not_dvd hpm, pow_zero]) _ _
  · rw [reduction_localSymbol_of_ne m p hq hqp, map_zpow]
    congr 1
    apply Units.ext
    simp [val_reduction]

/-- The symbol is trivial on `1 + p^r ℤ_p`, where `p^r` is the `p`-part of `m`. -/
theorem localSymbol_eq_one (a : ℚ_[p]ˣ)
    (h : ‖(a : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(m.factorization p : ℤ)))
    (h1 : ‖(a : ℚ_[p]) - 1‖ < 1) : localSymbol m p a = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.out.ne_one
  have hnorm : ‖(a : ℚ_[p])‖ = 1 := by
    have h2 : ‖(a : ℚ_[p]) - 1‖ ≠ ‖(1 : ℚ_[p])‖ := by rw [norm_one]; exact h1.ne
    have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2
    rw [sub_add_cancel, norm_one, max_eq_right h1.le] at h3
    exact h3
  have hv : (a : ℚ_[p]).valuation = 0 := by
    have h4 := Padic.norm_eq_zpow_neg_valuation a.ne_zero
    rw [hnorm] at h4
    have h5 : (p : ℝ) ^ (-(a : ℚ_[p]).valuation) = (p : ℝ) ^ (0 : ℤ) := by
      rw [← h4, zpow_zero]
    have h6 := (zpow_right_inj₀ (by positivity) hp1).1 h5
    linarith
  have hu : ((unitPart p a : ℤ_[p]) : ℚ_[p]) = a := by
    rw [coe_unitPart, hv, neg_zero, zpow_zero, mul_one]
  have hred : Units.map (PadicInt.toZModPow (m.factorization p)).toMonoidHom (unitPart p a) = 1 := by
    apply Units.ext
    change PadicInt.toZModPow (m.factorization p) (unitPart p a : ℤ_[p]) = 1
    rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow (m.factorization p)), ← map_sub,
      ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    change ‖((unitPart p a : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ _
    rw [hu]
    exact h
  rw [localSymbol_apply, map_inv, hred, hv, zpow_zero, inv_one]
  exact (crtUnits m p).map_one

end Modulus

section Rational

variable (m : ℕ) [NeZero m]

/-- The sign symbol `ℚˣ → (ℤ/m)ˣ`, `α ↦ ±1`. -/
def signUnit : ℚˣ →* (ZMod m)ˣ where
  toFun α := if (α : ℚ) < 0 then -1 else 1
  map_one' := by simp
  map_mul' a b := by
    have ha := a.ne_zero
    have hb := b.ne_zero
    rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb'
    · simp [Units.val_mul, ha', hb', not_lt.2 (mul_pos_of_neg_of_neg ha' hb').le]
    · simp [Units.val_mul, ha', not_lt.2 hb'.le, mul_neg_of_neg_of_pos ha' hb']
    · simp [Units.val_mul, not_lt.2 ha'.le, hb', mul_neg_of_pos_of_neg ha' hb']
    · simp [Units.val_mul, not_lt.2 ha'.le, not_lt.2 hb'.le, not_lt.2 (mul_pos ha' hb').le]

/-- The local symbol at `p` of a rational unit. -/
def ratLocalSymbol (p : ℕ) [Fact p.Prime] : ℚˣ →* (ZMod m)ˣ :=
  (localSymbol m p).comp (Units.map (Rat.castHom ℚ_[p]).toMonoidHom)

/-- The local symbol at the prime `p`, indexed by `Nat.Primes`. -/
def primeSymbol (p : Nat.Primes) : ℚˣ →* (ZMod m)ˣ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  ratLocalSymbol m p

theorem valuation_ratCast_unit (p : ℕ) [Fact p.Prime] (α : ℚˣ) :
    ((Units.map (Rat.castHom ℚ_[p]).toMonoidHom α : ℚ_[p]ˣ) : ℚ_[p]).valuation =
      padicValRat p α :=
  Padic.valuation_ratCast _

/-- The local symbol at `p` of a rational unit is trivial when `p ∤ m` and `v_p(α) = 0`. -/
theorem ratLocalSymbol_eq_one (p : ℕ) [hp : Fact p.Prime] (α : ℚˣ) (hpm : ¬p ∣ m)
    (hv : padicValRat p α = 0) : ratLocalSymbol m p α = 1 := by
  rw [ratLocalSymbol, MonoidHom.comp_apply, localSymbol_of_not_dvd m p hpm, valuation_ratCast_unit,
    hv, zpow_zero]

theorem mulSupport_primeSymbol_finite (α : ℚˣ) :
    (Function.mulSupport fun p : Nat.Primes => primeSymbol m p α).Finite := by
  set N := m * (α : ℚ).num.natAbs * (α : ℚ).den with hN
  have hN0 : N ≠ 0 := by
    have h1 : (α : ℚ).num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 α.ne_zero)
    exact mul_ne_zero (mul_ne_zero (NeZero.ne m) h1) (α : ℚ).den_nz
  refine (N.primeFactors.finite_toSet.preimage Subtype.val_injective.injOn).subset ?_
  intro p hp
  have hp' : primeSymbol m p α ≠ 1 := hp
  simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_primeFactors]
  refine ⟨p.2, ?_, hN0⟩
  by_contra hdvd
  apply hp'
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  change ratLocalSymbol m p α = 1
  refine ratLocalSymbol_eq_one m p α (fun h => hdvd ?_) ?_
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  · rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd,
      padicValNat.eq_zero_of_not_dvd, Nat.cast_zero, sub_zero]
    · exact fun h => hdvd (Dvd.dvd.mul_left h _)
    · exact fun h => hdvd (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)

/-- The product of the local symbols at all primes. -/
def symbolProduct : ℚˣ →* (ZMod m)ˣ where
  toFun α := ∏ᶠ p : Nat.Primes, primeSymbol m p α
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    exact finprod_mul_distrib (mulSupport_primeSymbol_finite m a)
      (mulSupport_primeSymbol_finite m b)

theorem symbolProduct_apply (α : ℚˣ) :
    symbolProduct m α = ∏ᶠ p : Nat.Primes, primeSymbol m p α := rfl

/-- The rational unit given by a prime number. -/
def primeRatUnit (ℓ : ℕ) (hℓ : ℓ.Prime) : ℚˣ :=
  Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.2 hℓ.ne_zero)

/-- Two homomorphisms on `ℚˣ` agree when they agree on `-1` and on all primes. -/
theorem ratUnits_hom_ext {G : Type*} [CommGroup G] (f g : ℚˣ →* G)
    (hneg : f (-1) = g (-1))
    (hprime : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), f (primeRatUnit ℓ hℓ) = g (primeRatUnit ℓ hℓ)) :
    f = g := by
  have hnat : ∀ n : ℕ, ∀ hn : (n : ℚ) ≠ 0, f (Units.mk0 (n : ℚ) hn) = g (Units.mk0 (n : ℚ) hn) := by
    intro n
    induction n using induction_on_primes with
    | zero => intro hn; exact absurd Nat.cast_zero hn
    | one =>
      intro hn
      have : Units.mk0 ((1 : ℕ) : ℚ) hn = 1 := Units.ext (by simp)
      rw [this, map_one, map_one]
    | prime_mul ℓ a hℓ ih =>
      intro hn
      have ha : (a : ℚ) ≠ 0 := by
        intro h
        apply hn
        rw [Nat.cast_mul, h, mul_zero]
      have : Units.mk0 ((ℓ * a : ℕ) : ℚ) hn = primeRatUnit ℓ hℓ * Units.mk0 (a : ℚ) ha :=
        Units.ext (by simp [primeRatUnit])
      rw [this, map_mul, map_mul, hprime, ih ha]
  ext α
  have hnum : ((α : ℚ).num.natAbs : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 α.ne_zero))
  have hden : ((α : ℚ).den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (α : ℚ).den_nz
  have hsign : ∃ s : ℚˣ, (s = 1 ∨ s = -1) ∧
      α = s * Units.mk0 _ hnum * (Units.mk0 _ hden)⁻¹ := by
    rcases le_or_gt 0 (α : ℚ).num with h | h
    · refine ⟨1, Or.inl rfl, Units.ext ?_⟩
      simp only [one_mul, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h), ← div_eq_mul_inv,
        Rat.num_div_den]
    · refine ⟨-1, Or.inr rfl, Units.ext ?_⟩
      simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h), neg_one_mul, neg_neg,
        ← div_eq_mul_inv, Rat.num_div_den]
  obtain ⟨s, hs, hα⟩ := hsign
  have hfs : f s = g s := by
    rcases hs with rfl | rfl
    · rw [map_one, map_one]
    · exact hneg
  rw [hα, map_mul, map_mul, map_mul, map_mul, hfs, hnat _ hnum, map_inv, map_inv, hnat _ hden]

theorem reduction_ratLocalSymbol_self (q : ℕ) [Fact q.Prime] (α : ℚˣ) :
    reduction m q (ratLocalSymbol m q α) =
      (Units.map (PadicInt.toZModPow (m.factorization q)).toMonoidHom
        (unitPart q (Units.map (Rat.castHom ℚ_[q]).toMonoidHom α)))⁻¹ :=
  reduction_localSymbol_self m q _

theorem reduction_ratLocalSymbol_of_ne {q : ℕ} (hq : q.Prime) (p : ℕ) [hp : Fact p.Prime]
    (hqp : q ≠ p) (α : ℚˣ) :
    reduction m q (ratLocalSymbol m p α) =
      ZMod.unitOfCoprime p (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out hq).2
        hqp.symm)) ^ padicValRat p α := by
  rw [ratLocalSymbol, MonoidHom.comp_apply, reduction_localSymbol_of_ne m p hq hqp,
    valuation_ratCast_unit]

theorem coe_unitPart_ratCast (p : ℕ) [Fact p.Prime] (α : ℚˣ) :
    ((unitPart p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom α) : ℤ_[p]) : ℚ_[p]) =
      (α : ℚ) * (p : ℚ_[p]) ^ (-padicValRat p α) := by
  rw [coe_unitPart, valuation_ratCast_unit]
  rfl

theorem padicValRat_neg_one (p : ℕ) : padicValRat p ((-1 : ℚˣ) : ℚ) = 0 := by
  rw [Units.val_neg, Units.val_one, padicValRat.neg, padicValRat.one]

theorem padicValRat_primeRatUnit (p : ℕ) [Fact p.Prime] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    padicValRat p (primeRatUnit ℓ hℓ : ℚ) = if p = ℓ then 1 else 0 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [primeRatUnit, Units.val_mk0, padicValRat.of_nat]
  split_ifs with h
  · subst h
    rw [padicValNat_self, Nat.cast_one]
  · rw [padicValNat_primes h, Nat.cast_zero]

/-- The product formula: `sign(α) · ∏_p σ_p(α) = 1` in `(ℤ/m)ˣ` for every `α ∈ ℚˣ`. -/
theorem product_formula (α : ℚˣ) : signUnit m α * symbolProduct m α = 1 := by
  refine eq_one_of_reduction m _ fun q hq => ?_
  have : Fact q.Prime := ⟨hq⟩
  let q' : Nat.Primes := ⟨q, hq⟩
  have hfin := fun x : ℚˣ => mulSupport_primeSymbol_finite m x
  -- The reduction of the product, as a homomorphism in `α`.
  let Φ : ℚˣ →* (ZMod (q ^ m.factorization q))ˣ := (reduction m q).comp (signUnit m * symbolProduct m)
  have hΦ : ∀ x, Φ x = reduction m q (signUnit m x) *
      ∏ᶠ p : Nat.Primes, reduction m q (primeSymbol m p x) := fun x => by
    change reduction m q (signUnit m x * symbolProduct m x) = _
    rw [map_mul, symbolProduct_apply, MonoidHom.map_finprod _ (hfin x)]
  have hother : ∀ (x : ℚˣ) (p : Nat.Primes), p ≠ q' → padicValRat p x = 0 →
      reduction m q (primeSymbol m p x) = 1 := by
    intro x p hpq hv
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hne : q ≠ (p : ℕ) := fun h => hpq (Subtype.ext h.symm)
    change reduction m q (ratLocalSymbol m p x) = 1
    rw [reduction_ratLocalSymbol_of_ne m hq p hne, hv, zpow_zero]
  have hself : ∀ x : ℚˣ, reduction m q (primeSymbol m q' x) =
      (Units.map (PadicInt.toZModPow (m.factorization q)).toMonoidHom
        (unitPart q (Units.map (Rat.castHom ℚ_[q]).toMonoidHom x)))⁻¹ :=
    fun x => reduction_ratLocalSymbol_self m q x
  have hred_neg : reduction m q (-1) = -1 := by
    apply Units.ext
    rw [val_reduction, Units.val_neg, Units.val_one, map_neg, map_one, Units.val_neg,
      Units.val_one]
  have hΦ1 : Φ = 1 := by
    refine ratUnits_hom_ext Φ 1 ?_ ?_
    · -- the generator `-1`
      rw [hΦ, MonoidHom.one_apply]
      have hsign : signUnit m (-1) = -1 := by
        change (if ((-1 : ℚˣ) : ℚ) < 0 then -1 else 1) = _
        rw [ite_eq_left (by norm_num)]
      rw [hsign, hred_neg, finprod_eq_single _ q' fun p hp =>
        hother (-1) p hp (padicValRat_neg_one p), hself]
      have hu : Units.map (PadicInt.toZModPow (m.factorization q)).toMonoidHom
          (unitPart q (Units.map (Rat.castHom ℚ_[q]).toMonoidHom (-1))) = -1 := by
        have h1 : unitPart q (Units.map (Rat.castHom ℚ_[q]).toMonoidHom (-1)) = -1 := by
          apply Units.ext
          apply PadicInt.ext
          rw [coe_unitPart_ratCast, padicValRat_neg_one, neg_zero, zpow_zero, mul_one]
          simp
        rw [h1]
        apply Units.ext
        simp
      rw [hu, inv_neg_one, neg_one_mul, neg_neg]
    · -- the generators `ℓ`
      intro ℓ hℓ
      rw [hΦ, MonoidHom.one_apply]
      have hsign : signUnit m (primeRatUnit ℓ hℓ) = 1 := by
        change (if ((primeRatUnit ℓ hℓ : ℚˣ) : ℚ) < 0 then -1 else 1) = _
        rw [ite_eq_right]
        rw [primeRatUnit, Units.val_mk0, not_lt]
        exact Nat.cast_nonneg _
      rw [hsign, map_one, one_mul]
      by_cases hqℓ : q = ℓ
      · subst hqℓ
        rw [finprod_eq_single _ q' fun p hp => hother _ p hp (by
          have : Fact (p : ℕ).Prime := ⟨p.2⟩
          rw [padicValRat_primeRatUnit, ite_eq_right fun h => hp (Subtype.ext h)]), hself]
        have h1 : unitPart q (Units.map (Rat.castHom ℚ_[q]).toMonoidHom (primeRatUnit q hq)) = 1 := by
          apply Units.ext
          apply PadicInt.ext
          rw [coe_unitPart_ratCast, padicValRat_primeRatUnit, ite_eq_left rfl]
          have hq0 : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast hq.ne_zero
          simp [primeRatUnit, hq0]
        rw [h1, map_one, inv_one]
      · let ℓ' : Nat.Primes := ⟨ℓ, hℓ⟩
        have hne' : q' ≠ ℓ' := fun h => hqℓ (congrArg Subtype.val h)
        rw [finprod_eq_prod_of_mulSupport_subset (s := {q', ℓ'}), Finset.prod_pair hne', hself]
        · have : Fact ℓ.Prime := ⟨hℓ⟩
          change _ * reduction m q (ratLocalSymbol m ℓ (primeRatUnit ℓ hℓ)) = 1
          rw [reduction_ratLocalSymbol_of_ne m hq ℓ hqℓ, padicValRat_primeRatUnit, ite_eq_left rfl,
            zpow_one, inv_mul_eq_one]
          apply Units.ext
          have hv : padicValRat q (primeRatUnit ℓ hℓ : ℚ) = 0 := by
            rw [padicValRat_primeRatUnit, ite_eq_right hqℓ]
          have h2 : ((unitPart q (Units.map (Rat.castHom ℚ_[q]).toMonoidHom
              (primeRatUnit ℓ hℓ)) : ℤ_[q])) = (ℓ : ℤ_[q]) := by
            apply PadicInt.ext
            rw [coe_unitPart_ratCast, hv, neg_zero, zpow_zero, mul_one]
            simp [primeRatUnit]
          change PadicInt.toZModPow (m.factorization q)
            ((unitPart q (Units.map (Rat.castHom ℚ_[q]).toMonoidHom (primeRatUnit ℓ hℓ)) : ℤ_[q])) = _
          rw [h2, map_natCast, ZMod.coe_unitOfCoprime]
        · intro p hp
          have hp' : reduction m q (primeSymbol m p (primeRatUnit ℓ hℓ)) ≠ 1 := hp
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          by_contra hcon
          push Not at hcon
          apply hp'
          refine hother _ p hcon.1 ?_
          have : Fact (p : ℕ).Prime := ⟨p.2⟩
          rw [padicValRat_primeRatUnit, ite_eq_right fun h => hcon.2 (Subtype.ext h)]
  have := congrArg (fun f : ℚˣ →* _ => f α) hΦ1
  exact this

end Rational

end Langlands.Global.CyclotomicSymbol
