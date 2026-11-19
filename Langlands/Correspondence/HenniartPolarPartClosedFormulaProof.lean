import Langlands.Correspondence.HenniartPolarPart
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The closed formula for the polar-part count

The proof of Lemma 3.2 of the operator's numerical local Langlands route note
uses Möbius inversion for the field of coefficients and for the support gcd.
-/

noncomputable section

namespace Langlands.Henniart

open ArithmeticFunction Numerical

private theorem sum_moebius_divisors (n : ℕ) :
    (∑ e ∈ n.divisors, moebius e) = if n = 1 then 1 else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

private theorem sum_moebius_support {D g : ℕ} (hD : D ≠ 0) (hg : g ∣ D) :
    (∑ e ∈ D.divisors, if e ∣ g then moebius e else 0) = if g = 1 then 1 else 0 := by
  rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hD hg, sum_moebius_divisors]

private theorem sum_moebius_degree (d : ℕ) {f : ℕ} (hf : 0 < f) :
    (∑ i ∈ f.divisors, if d ∣ i then moebius (f / i) else 0) = if f = d then 1 else 0 := by
  have hs (n : ℕ) (hn : 0 < n) :
      (∑ i ∈ n.divisors, if i = d then (1 : ℤ) else 0) = if d ∣ n then 1 else 0 := by
    simp [Nat.mem_divisors, hn.ne']
  rw [← Nat.sum_divisorsAntidiagonal' (fun e i => if d ∣ i then moebius e else 0)]
  simpa only [Int.cast_id, mul_ite, mul_one, mul_zero] using
    (sum_eq_iff_sum_mul_moebius_eq (R := ℤ)).mp hs f hf

private theorem mul_card_subtype {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (w : ℤ) : w * (Nat.card {a // P a} : ℤ) = ∑ a : α, if P a then w else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter, Finset.sum_const,
    Finset.subtype_univ, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

/-- The product of the two Möbius indicators counts the intersection of the conditions. -/
private theorem card_degree_and_support {α : Type*} [Fintype α]
    (degree support : α → ℕ) {f D : ℕ} (hf : 0 < f) (hD : D ≠ 0)
    (hs : ∀ a, support a ∣ D) :
    (Nat.card {a // f = degree a ∧ support a = 1} : ℤ) =
      ∑ i ∈ f.divisors, moebius (f / i) * ∑ e ∈ D.divisors,
        moebius e * (Nat.card {a // degree a ∣ i ∧ e ∣ support a} : ℤ) := by
  classical
  simp_rw [Finset.mul_sum, ← mul_assoc, mul_card_subtype]
  calc
    (Nat.card {a // f = degree a ∧ support a = 1} : ℤ) =
        ∑ a : α, if f = degree a ∧ support a = 1 then 1 else 0 := by
      simpa only [one_mul] using mul_card_subtype (fun a => f = degree a ∧ support a = 1) 1
    _ = ∑ a : α, ∑ i ∈ f.divisors, ∑ e ∈ D.divisors,
        if degree a ∣ i ∧ e ∣ support a then moebius (f / i) * moebius e else 0 := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h (i e : ℕ) :
          (if degree a ∣ i ∧ e ∣ support a then moebius (f / i) * moebius e else 0) =
            (if degree a ∣ i then moebius (f / i) else 0) *
            (if e ∣ support a then moebius e else 0) := by
        by_cases hi : degree a ∣ i <;> by_cases he : e ∣ support a <;> simp [hi, he]
      simp_rw [h, ← Finset.mul_sum, sum_moebius_support hD (hs a), ← Finset.sum_mul,
        sum_moebius_degree _ hf]
      by_cases hi : f = degree a <;> by_cases he : support a = 1 <;> simp [hi, he]
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

section FiniteFields

open IntermediateField Polynomial

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Finite k] [Finite L]

omit [Finite k] in
private theorem intermediateField_le_iff_dvd (E F : IntermediateField k L) :
    E ≤ F ↔ Module.finrank k E ∣ Module.finrank k F := by
  refine ⟨finrank_dvd_of_le_right, fun h => ?_⟩
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd h
  let _ := Fintype.ofFinite E
  let _ : IsSplittingField k E (X ^ Fintype.card E - X) := FiniteField.isSplittingField_sub E k
  rw [← (F.val.comp φ).fieldRange_of_normal]
  rintro _ ⟨x, rfl⟩
  exact (φ x).property

private theorem exists_intermediateField_degree (p : ℕ) [Fact p.Prime] [CharP k p]
    {i : ℕ} (hi : 0 < i) (hd : i ∣ Module.finrank k L) :
    ∃ E : IntermediateField k L, Module.finrank k E = i := by
  let _ : NeZero i := ⟨hi.ne'⟩
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    ((FiniteField.finrank_extension k p i).symm ▸ hd)
  exact ⟨φ.fieldRange, φ.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans
    (FiniteField.finrank_extension k p i)⟩

end FiniteFields

private abbrev EndpointMaps (K : Type*) [Field K] (m : ℕ) :=
  {c : Fin (m + 1) → K // c 0 ≠ 0 ∧ c (Fin.last m) ≠ 0}

private theorem card_endpointMaps (K : Type*) [Field K] [Finite K] (m : ℕ) :
    (Nat.card (EndpointMaps K m) : ℤ) =
      if m = 0 then (Nat.card K : ℤ) - 1
      else ((Nat.card K : ℤ) - 1) ^ 2 * (Nat.card K : ℤ) ^ (m - 1) := by
  have hnonzero : Nat.card {a : K // a ≠ 0} = Nat.card K - 1 := by
    rw [← Nat.card_congr (unitsEquivNeZero (G₀ := K)), Nat.card_units]
  have hpos : 1 ≤ Nat.card K := Nat.card_pos
  cases m with
  | zero =>
    let equiv : EndpointMaps K 0 ≃ {a : K // a ≠ 0} :=
      { toFun := fun c => ⟨c.val 0, c.property.1⟩
        invFun := fun a => ⟨fun _ => a.val, a.property, a.property⟩
        left_inv := fun c => Subtype.ext (funext fun j => by rw [Fin.eq_zero j])
        right_inv := fun _ => rfl }
    rw [Nat.card_congr equiv, hnonzero, Nat.cast_sub hpos, Nat.cast_one, ite_eq_left rfl]
  | succ t =>
    let splitEndpoints : (K × K) × (Fin t → K) ≃ (Fin (t + 2) → K) :=
      (Equiv.prodAssoc K K (Fin t → K)).trans
        ((Equiv.prodCongr (Equiv.refl K) (Fin.snocEquiv fun _ : Fin (t + 1) => K)).trans
          (Fin.consEquiv fun _ : Fin (t + 2) => K))
    have hEndpoints (x : (K × K) × (Fin t → K)) :
        x.1.1 ≠ 0 ∧ x.1.2 ≠ 0 ↔
          splitEndpoints x 0 ≠ 0 ∧ splitEndpoints x (Fin.last (t + 1)) ≠ 0 := by
      simp only [splitEndpoints, Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply,
        Prod.map, Equiv.refl_apply, Fin.consEquiv_apply, Fin.snocEquiv_apply, Fin.cons_zero,
        Fin.cons_last, Fin.snoc_last]
    let equiv : EndpointMaps K (t + 1) ≃
        ({a : K // a ≠ 0} × {a : K // a ≠ 0}) × (Fin t → K) :=
      (splitEndpoints.subtypeEquiv hEndpoints).symm.trans
        (Equiv.prodSubtypeFstEquivSubtypeProd.trans
          (Equiv.prodCongr Equiv.subtypeProdEquivProd (Equiv.refl _)))
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod, hnonzero, Nat.card_fun,
      Nat.card_fin, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one, Nat.cast_pow,
      ite_eq_right (Nat.succ_ne_zero _), Nat.add_sub_cancel, pow_two]

private theorem dvd_polarSupportGcd_iff {K : Type*} [Field K] {m e : ℕ}
    (c : Fin (m + 1) → K) :
    e ∣ polarSupportGcd c ↔ ∀ j : Fin (m + 1), ¬ e ∣ (j : ℕ) → c j = 0 := by
  classical
  unfold polarSupportGcd
  rw [Finset.dvd_gcd_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · by_contra hzero
    have hpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero fun hz => hj (hz.symm ▸ Nat.dvd_zero e)
    exact hj (h j ⟨hpos, hzero⟩)
  · by_contra hdiv
    exact hj.2 (h j hdiv)

private theorem polarSupportGcd_dvd_last {K : Type*} [Field K] {m : ℕ}
    (c : EndpointMaps K m) : polarSupportGcd c.val ∣ m := by
  classical
  by_cases hm : m = 0
  · subst m
    exact Nat.dvd_zero _
  · unfold polarSupportGcd
    change _ ∣ ((Fin.last m : Fin (m + 1)) : ℕ)
    apply Finset.gcd_dvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hm, c.property.2⟩

/-- Restrict to the indices divisible by `e`, and view their coefficients in `E`. -/
private def restrictSupportedMaps {k L : Type*} [Field k] [Field L] [Algebra k L]
    (E : IntermediateField k L) {m e : ℕ} (he : 0 < e) (hem : e ∣ m) :
    {c : EndpointMaps L m // (∀ j, c.val j ∈ E) ∧
      ∀ j : Fin (m + 1), ¬ e ∣ (j : ℕ) → c.val j = 0} ≃ EndpointMaps E (m / e) := by
  let SupportedMaps := {c : EndpointMaps L m // (∀ j, c.val j ∈ E) ∧
    ∀ j : Fin (m + 1), ¬ e ∣ (j : ℕ) → c.val j = 0}
  let mulIndex (j : Fin (m / e + 1)) : Fin (m + 1) :=
    ⟨(j : ℕ) * e, Nat.lt_succ_of_le
      ((Nat.mul_le_mul_right e (Nat.le_of_lt_succ j.isLt)).trans_eq (Nat.div_mul_cancel hem))⟩
  let divIndex (j : Fin (m + 1)) : Fin (m / e + 1) :=
    ⟨(j : ℕ) / e, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ j.isLt))⟩
  have mulIndex_zero : mulIndex 0 = 0 := Fin.ext (Nat.zero_mul e)
  have mulIndex_last : mulIndex (Fin.last (m / e)) = Fin.last m :=
    Fin.ext (Nat.div_mul_cancel hem)
  have divIndex_zero : divIndex 0 = 0 := Fin.ext (Nat.zero_div e)
  have divIndex_last : divIndex (Fin.last m) = Fin.last (m / e) := rfl
  have mulIndex_divIndex (j : Fin (m + 1)) (hj : e ∣ (j : ℕ)) : mulIndex (divIndex j) = j :=
    Fin.ext (Nat.div_mul_cancel hj)
  have divIndex_mulIndex (j : Fin (m / e + 1)) : divIndex (mulIndex j) = j :=
    Fin.ext (Nat.mul_div_cancel _ he)
  let restrict (c : SupportedMaps) : EndpointMaps E (m / e) :=
    ⟨fun j => ⟨c.val.val (mulIndex j), c.property.1 _⟩, by
      constructor <;> apply (map_ne_zero E.val).mp
      · change c.val.val (mulIndex 0) ≠ 0
        rw [mulIndex_zero]
        exact c.val.property.1
      · change c.val.val (mulIndex (Fin.last (m / e))) ≠ 0
        rw [mulIndex_last]
        exact c.val.property.2⟩
  let fill (c : EndpointMaps E (m / e)) (j : Fin (m + 1)) : L :=
    if e ∣ (j : ℕ) then (c.val (divIndex j) : L) else 0
  let extend (c : EndpointMaps E (m / e)) : SupportedMaps :=
    ⟨⟨fill c, by
        constructor
        · simp only [fill, Fin.val_zero, ite_eq_left (Nat.dvd_zero e), divIndex_zero]
          exact (map_ne_zero E.val).mpr c.property.1
        · simp only [fill, Fin.val_last, ite_eq_left hem, divIndex_last]
          exact (map_ne_zero E.val).mpr c.property.2⟩, by
      constructor
      · intro j
        dsimp only [fill]
        split
        · exact (c.val (divIndex j)).property
        · exact E.zero_mem
      · intro j hj
        exact ite_eq_right hj⟩
  refine ⟨restrict, extend, ?_, ?_⟩
  · intro c
    apply Subtype.ext
    apply Subtype.ext
    funext j
    change (if e ∣ (j : ℕ) then c.val.val (mulIndex (divIndex j)) else 0) = c.val.val j
    by_cases hj : e ∣ (j : ℕ)
    · rw [ite_eq_left hj, mulIndex_divIndex j hj]
    · rw [ite_eq_right hj, c.property.2 j hj]
  · intro c
    apply Subtype.ext
    funext j
    apply Subtype.ext
    change (if e ∣ (j : ℕ) * e then (c.val (divIndex (mulIndex j)) : L) else 0) = (c.val j : L)
    rw [ite_eq_left (dvd_mul_left e (j : ℕ)), divIndex_mulIndex]

private theorem card_polarParts_closed_sum {k L : Type*} [Field k] [Field L] [Algebra k L]
    [Finite k] [Finite L] (p : ℕ) [Fact p.Prime] [CharP k p] (r m : ℕ) (hr : 0 < r) :
    (Nat.card (polarParts k L r m) : ℤ) =
      ∑ i ∈ (Module.finrank k L).divisors, moebius (Module.finrank k L / i) *
        ∑ e ∈ (Nat.gcd r m).divisors, moebius e *
          (if m / e = 0 then (Nat.card k : ℤ) ^ i - 1
           else ((Nat.card k : ℤ) ^ i - 1) ^ 2 * (Nat.card k : ℤ) ^ (i * (m / e - 1))) := by
  classical
  let degree (c : EndpointMaps L m) := Module.finrank k (IntermediateField.adjoin k (Set.range c.val))
  let support (c : EndpointMaps L m) := Nat.gcd r (polarSupportGcd c.val)
  let f := Module.finrank k L
  let D := Nat.gcd r m
  have hf : 0 < f := Module.finrank_pos
  have hD : D ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left r m) hr).ne'
  have hSupportDvd (c : EndpointMaps L m) : support c ∣ D :=
    Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans (polarSupportGcd_dvd_last c))
  have hFull (c : EndpointMaps L m) :
      f = degree c ↔ IntermediateField.adjoin k (Set.range c.val) = ⊤ := by
    change Module.finrank k L = Module.finrank k
      (IntermediateField.adjoin k (Set.range c.val)) ↔ _
    rw [← IntermediateField.finrank_top' (F := k) (E := L),
      eq_comm, ← IntermediateField.eq_iff_finrank_eq_of_le le_top]
  let polarEquiv : {c : EndpointMaps L m // IsPolarPart k r m c.val} ≃ polarParts k L r m :=
    Equiv.subtypeSubtypeEquivSubtype fun hc => ⟨hc.1, hc.2.1⟩
  let equiv : {c : EndpointMaps L m // f = degree c ∧ support c = 1} ≃ polarParts k L r m :=
    (Equiv.subtypeEquivRight fun c => by
      rw [hFull]
      exact ⟨fun h => ⟨c.property.1, c.property.2, h.1, h.2⟩,
        fun h => ⟨h.2.2.1, h.2.2.2⟩⟩).trans polarEquiv
  let _ := Fintype.ofFinite (EndpointMaps L m)
  rw [← Nat.card_congr equiv, card_degree_and_support degree support hf hD hSupportDvd]
  refine Finset.sum_congr rfl fun i hi => congrArg (moebius (f / i) * ·) ?_
  obtain ⟨E, hE⟩ := exists_intermediateField_degree (k := k) (L := L) p
    (Nat.pos_of_mem_divisors hi) (Nat.dvd_of_mem_divisors hi)
  have hValues (c : EndpointMaps L m) : degree c ∣ i ↔ ∀ j, c.val j ∈ E := by
    change Module.finrank k (IntermediateField.adjoin k (Set.range c.val)) ∣ i ↔ _
    rw [← hE, ← intermediateField_le_iff_dvd, IntermediateField.adjoin_le_iff]
    exact Set.range_subset_iff
  refine Finset.sum_congr rfl fun e he => congrArg (moebius e * ·) ?_
  have her : e ∣ r := (Nat.dvd_of_mem_divisors he).trans (Nat.gcd_dvd_left r m)
  have hem : e ∣ m := (Nat.dvd_of_mem_divisors he).trans (Nat.gcd_dvd_right r m)
  have hSupport (c : EndpointMaps L m) :
      e ∣ support c ↔ ∀ j : Fin (m + 1), ¬ e ∣ (j : ℕ) → c.val j = 0 := by
    change e ∣ Nat.gcd r (polarSupportGcd c.val) ↔ _
    rw [Nat.dvd_gcd_iff, and_iff_right her, dvd_polarSupportGcd_iff]
  let restrictedEquiv := (Equiv.subtypeEquivRight fun c => and_congr (hValues c) (hSupport c)).trans
    (restrictSupportedMaps E (Nat.pos_of_mem_divisors he) hem)
  rw [Nat.card_congr restrictedEquiv, card_endpointMaps, Module.natCard_eq_pow_finrank (K := k),
    hE, Nat.cast_pow, pow_mul]

private theorem card_polarParts_eq_mul_orbit_count {k L : Type*} [Field k] [Field L]
    [Algebra k L] (r m : ℕ) :
    Nat.card (polarParts k L r m) = Nat.card Gal(L/k) * polarPartCountOf k L r m := by
  have hfree (c : polarParts k L r m) : MulAction.stabilizer Gal(L/k) c = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    rw [Subgroup.mem_bot]
    have hc : IsPolarPart k r m c.val := c.property
    let E : IntermediateField k L := ⊤
    have h : (g : L →ₐ[k] L).comp E.val = (AlgHom.id k L).comp E.val := by
      apply IntermediateField.algHom_ext_of_eq_adjoin k hc.2.2.1.symm
      rintro _ ⟨j, rfl⟩
      exact congrFun (congrArg Subtype.val hg) j
    ext x
    exact DFunLike.congr_fun h (⟨x, IntermediateField.mem_top⟩ : E)
  rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree), Nat.card_prod, mul_comm]
  rfl

private theorem natCard_polarBaseField (q : ℕ) (hq : IsPrimePow q) [Fact q.minFac.Prime] :
    Nat.card (polarBaseField q) = q := by
  have hExp : q.factorization q.minFac ≠ 0 := by
    intro h
    have hq' := hq.minFac_pow_factorization_eq
    rw [h, pow_zero] at hq'
    exact hq.ne_one hq'.symm
  exact (GaloisField.card _ _ hExp).trans hq.minFac_pow_factorization_eq

private theorem polarPartCount_closed_sum (q : ℕ) (hq : IsPrimePow q) (n f s : ℕ)
    (hn : 0 < n) (hf : 0 < f) (hfn : f ∣ n) (hfs : f ∣ s) :
    (f : ℤ) * (polarPartCount q n f s : ℤ) =
      ∑ i ∈ f.divisors, moebius (f / i) *
        ∑ e ∈ (Nat.gcd (n / f) (s / f)).divisors, moebius e *
          (if s / f / e = 0 then (q : ℤ) ^ i - 1 else
            ((q : ℤ) ^ i - 1) ^ 2 * (q : ℤ) ^ (i * (s / f / e - 1))) := by
  let : Fact q.minFac.Prime := ⟨Nat.minFac_prime hq.ne_one⟩
  let : NeZero f := ⟨hf.ne'⟩
  let k := polarBaseField q
  let L := polarExtensionField q f
  have hr : 0 < n / f := Nat.div_pos (Nat.le_of_dvd hn hfn) hf
  have horbit := card_polarParts_eq_mul_orbit_count (k := k) (L := L) (n / f) (s / f)
  rw [show Nat.card (Gal(L/k)) = f from FiniteField.natCard_algEquiv_extension k q.minFac f]
    at horbit
  have hcard := card_polarParts_closed_sum (k := k) (L := L) q.minFac (n / f) (s / f) hr
  rw [show Module.finrank k L = f from FiniteField.finrank_extension k q.minFac f,
    show Nat.card k = q from natCard_polarBaseField q hq] at hcard
  unfold polarPartCount
  rw [dite_eq_left ⟨hq, hn, hf, hfn, hfs⟩]
  change (f : ℤ) * (polarPartCountOf k L (n / f) (s / f) : ℤ) = _
  rw [← Nat.cast_mul, ← horbit]
  exact hcard

/-- The closed formula for `ν(n, f, s; q)` from route-note Lemma 3.2. -/
theorem polarPartClosedFormula : PolarPartClosedFormulaStatement := by
  intro q hq n f s hn hf hfn hfs
  constructor
  · intro hs
    rw [polarPartCount_closed_sum q hq n f s hn hf hfn hfs]
    have hm : 0 < s / f := Nat.div_pos (Nat.le_of_dvd hs hfs) hf
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc]
    apply congrArg (moebius (f / i) * ·)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hem : e ∣ s / f := (Nat.dvd_of_mem_divisors he).trans (Nat.gcd_dvd_right _ _)
    have hquot : 0 < s / f / e := Nat.div_pos (Nat.le_of_dvd hm hem) (Nat.pos_of_mem_divisors he)
    rw [ite_eq_right hquot.ne']
    ac_rfl
  · intro _
    constructor
    · intro hne
      have hr : n / f ≠ 1 := by
        intro h
        apply hne
        calc
          f = f * (n / f) := by rw [h, mul_one]
          _ = n := Nat.mul_div_cancel' hfn
      have hsum : ∑ e ∈ (n / f).divisors, moebius e = 0 := by
        rw [sum_moebius_divisors, ite_eq_right hr]
      have hzero := polarPartCount_closed_sum q hq n f 0 hn hf hfn (dvd_zero _)
      have hf0 : f ≠ 0 := (show 0 < f from hf).ne'
      simpa [← Finset.sum_mul, hsum, hf0] using hzero
    · simpa [Nat.div_self hn] using
        polarPartCount_closed_sum q hq n n 0 hn hn dvd_rfl (dvd_zero _)

end Langlands.Henniart
