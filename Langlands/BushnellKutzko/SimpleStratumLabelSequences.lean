import Langlands.BushnellKutzko.Labels

/-! # Extending and truncating the label sequences of BK94 (1.13) -/

noncomputable section

namespace Langlands.BushnellKutzko

open Polynomial Langlands.Henniart.Numerical Langlands.FieldTheory

namespace Label

variable {q : ℕ}

/-- The label with a single quadruple. -/
def single (x : LabelEntry q) : Label q := ⟨0, fun _ => x⟩

/-- The label obtained by appending one quadruple after the last entry. -/
def snoc (p : Label q) (x : LabelEntry q) : Label q where
  r := p.r + 1
  entry i := if h : (i : ℕ) < p.r + 1 then p.entry ⟨i, h⟩ else x

@[simp] theorem snoc_r (p : Label q) (x : LabelEntry q) : (p.snoc x).r = p.r + 1 := rfl

theorem snoc_entry_castSucc (p : Label q) (x : LabelEntry q) (i : Fin (p.r + 1)) :
    (p.snoc x).entry (Fin.castSucc i) = p.entry i := by
  simp [snoc, i.isLt]

theorem snoc_entry_last (p : Label q) (x : LabelEntry q) :
    (p.snoc x).entry (Fin.last (p.r + 1)) = x := by
  simp [snoc]

theorem degreeProd_eq_prod_ite (p : Label q) (k : ℕ) :
    p.degreeProd k = ∏ j : Fin (p.r + 1), if (j : ℕ) < k then (p.entry j).degree else 1 := by
  unfold degreeProd
  rw [Finset.prod_filter]

theorem degreeProd_of_le (p : Label q) {k : ℕ} (hk : p.r + 1 ≤ k) : p.degreeProd k = p.d := by
  rw [degreeProd_eq_prod_ite, d]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [ite_eq_left_iff]
  intro h
  exact absurd (by omega) h

theorem snoc_degreeProd_of_le (p : Label q) (x : LabelEntry q) {k : ℕ} (hk : k ≤ p.r + 1) :
    (p.snoc x).degreeProd k = p.degreeProd k := by
  rw [degreeProd_eq_prod_ite, degreeProd_eq_prod_ite]
  change (∏ j : Fin (p.r + 1 + 1), _) = _
  rw [Fin.prod_univ_castSucc]
  have hlast : ¬ ((Fin.last (p.r + 1) : Fin (p.r + 1 + 1)) : ℕ) < k := by
    simp only [Fin.val_last]
    omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false hlast), mul_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [snoc, j.isLt]

theorem snoc_d (p : Label q) (x : LabelEntry q) : (p.snoc x).d = p.d * x.degree := by
  unfold d
  change (∏ j : Fin (p.r + 1 + 1), _) = _
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp [snoc, j.isLt]
  · simp [snoc]

theorem snoc_degreeProd_succ_succ (p : Label q) (x : LabelEntry q) :
    (p.snoc x).degreeProd (p.r + 2) = p.d * x.degree := by
  rw [degreeProd_of_le _ (by simp), snoc_d]

theorem snoc_e (p : Label q) (x : LabelEntry q) : (p.snoc x).e = x.ramification :=
  congrArg LabelEntry.ramification (snoc_entry_last p x)

theorem single_d (x : LabelEntry q) : (single x).d = x.degree := by
  change ∏ _j : Fin 1, x.degree = x.degree
  simp

theorem single_e (x : LabelEntry q) : (single x).e = x.ramification := rfl

theorem snoc_injective {p p' : Label q} {x x' : LabelEntry q} (h : p.snoc x = p'.snoc x') :
    p = p' ∧ x = x' := by
  obtain ⟨r, entry⟩ := p
  obtain ⟨r', entry'⟩ := p'
  have hr : r = r' := by
    have := congrArg Label.r h
    simpa using this
  subst hr
  have hent : ∀ i : Fin (r + 1 + 1),
      (if h : (i : ℕ) < r + 1 then entry ⟨i, h⟩ else x) =
        (if h : (i : ℕ) < r + 1 then entry' ⟨i, h⟩ else x') := by
    simp only [snoc, Label.mk.injEq, heq_eq_eq, true_and] at h
    exact fun i => congrFun h i
  refine ⟨?_, ?_⟩
  · congr 1
    funext i
    have := hent (Fin.castSucc i)
    simpa [i.isLt] using this
  · have := hent (Fin.last (r + 1))
    simpa using this

end Label

/-- The polynomial condition on a quadruple: `φ` is a label polynomial of degree `d` over the
field `𝔽_{q^D}` that it is recorded with. -/
def LabelEntry.PolyOK (x : LabelEntry q) : Prop :=
  x.polynomial.poly ∈ irreduciblePolynomialLabels x.degree
    (polarExtensionField (labelFieldSize q) x.polynomial.exponent)

namespace Label

theorem snoc_entry_of_lt (p : Label q) (x : LabelEntry q) (i : Fin ((p.snoc x).r + 1))
    (h : (i : ℕ) < p.r + 1) : (p.snoc x).entry i = p.entry ⟨i, h⟩ := by
  simp [snoc, h]

theorem snoc_entry_of_eq (p : Label q) (x : LabelEntry q) (i : Fin ((p.snoc x).r + 1))
    (h : (i : ℕ) = p.r + 1) : (p.snoc x).entry i = x := by
  simp [snoc, h]

end Label

variable {q : ℕ}

/-- Every level of a label in `P^m_n` exceeds `m`. -/
theorem lt_level_of_mem_labelSet {m n a b : ℕ} {p : Label q} (hp : p ∈ labelSet m n a b q)
    (i : Fin (p.r + 1)) : m < (p.entry i).level := by
  obtain ⟨-, hmn, -, -, -, h0lev, -, -, -, -, hiii⟩ := hp
  induction i using Fin.cases with
  | zero => rw [h0lev]; exact hmn
  | succ j => exact (hiii j).1

/-- `P^{m+1}_n ⊆ P^m_n`. -/
theorem labelSet_succ_subset {m n a b : ℕ} : labelSet (m + 1) n a b q ⊆ labelSet m n a b q := by
  intro p hp
  obtain ⟨hq, hmn, ha, hb, hpos, h0lev, h0deg, h0ram, h0exp, h0poly, hiii⟩ := hp
  exact ⟨hq, by omega, ha, hb, hpos, h0lev, h0deg, h0ram, h0exp, h0poly,
    fun i => ⟨by have := (hiii i).1; omega, (hiii i).2⟩⟩

/-- A one-entry label of `P^m_n`. -/
theorem single_mem_labelSet {m n a b : ℕ} (hq : IsPrimePow q) (hmn : m < n) (ha : 0 < a)
    (hb : 0 < b) {x : LabelEntry q} (hlev : x.level = n) (hdeg : 0 < x.degree)
    (hdvd : x.degree ∣ b) (hram : x.ramification = Nat.gcd n a)
    (hexp : (x.polynomial.exponent : ℕ) = 1)
    (hpoly : x.polynomial.poly ∈ irreduciblePolynomialLabels x.degree
      (polarExtensionField (labelFieldSize q) x.polynomial.exponent)) :
    Label.single x ∈ labelSet m n a b q := by
  refine ⟨hq, hmn, ha, hb, fun _ => ⟨hdeg, ?_⟩, hlev, hdvd, ?_, hexp, hpoly, fun i => i.elim0⟩
  · change 0 < x.ramification
    rw [hram]
    exact Nat.gcd_pos_of_pos_right _ ha
  · change x.ramification = Nat.gcd x.level a
    rw [hram, hlev]

/-- Appending a quadruple of level `m + 1` to a label of `P^{m+1}_n` gives a label of `P^m_n`. -/
theorem snoc_mem_labelSet {m n a b : ℕ} {p : Label q} (hp : p ∈ labelSet (m + 1) n a b q)
    {x : LabelEntry q} (hlev : x.level = m + 1) (hdeg : 0 < x.degree)
    (hram : x.ramification = Nat.gcd (m + 1) p.e) (hexp : (x.polynomial.exponent : ℕ) = p.d)
    (hpoly : x.polynomial.poly ∈ irreduciblePolynomialLabels x.degree
      (polarExtensionField (labelFieldSize q) x.polynomial.exponent))
    (hdvd : p.d * x.degree ∣ b) :
    p.snoc x ∈ labelSet m n a b q := by
  have hlast : m + 1 < (p.entry (Fin.last p.r)).level := lt_level_of_mem_labelSet hp _
  obtain ⟨hq, hmn, ha, hb, hpos, h0lev, h0deg, h0ram, h0exp, h0poly, hiii⟩ := hp
  have h0 : (p.snoc x).entry 0 = p.entry 0 := Label.snoc_entry_of_lt p x 0 (by simp)
  refine ⟨hq, by omega, ha, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) < p.r + 1
    · rw [Label.snoc_entry_of_lt p x i hi]
      exact hpos _
    · rw [Label.snoc_entry_of_eq p x i (by have := i.isLt; simp at this; omega)]
      refine ⟨hdeg, ?_⟩
      rw [hram]
      exact Nat.gcd_pos_of_pos_left _ (by omega)
  · rw [h0]; exact h0lev
  · rw [h0]; exact h0deg
  · rw [h0]; exact h0ram
  · rw [h0]; exact h0exp
  · exact (congrArg LabelEntry.PolyOK h0).mpr h0poly
  · intro i
    have hi1 : ((i.succ : Fin ((p.snoc x).r + 1)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
    have hi2 : ((i.castSucc : Fin ((p.snoc x).r + 1)) : ℕ) = (i : ℕ) := Fin.val_castSucc i
    by_cases hi : (i : ℕ) < p.r
    · let j : Fin p.r := ⟨i, hi⟩
      have hs : (p.snoc x).entry i.succ = p.entry j.succ := by
        rw [Label.snoc_entry_of_lt p x i.succ (by omega)]
        congr 1
      have hc : (p.snoc x).entry i.castSucc = p.entry j.castSucc := by
        rw [Label.snoc_entry_of_lt p x i.castSucc (by omega)]
        congr 1
      have hd2 : (p.snoc x).degreeProd ((i : ℕ) + 2) = p.degreeProd ((j : ℕ) + 2) :=
        Label.snoc_degreeProd_of_le p x (by simp; omega)
      have hd1 : (p.snoc x).degreeProd ((i : ℕ) + 1) = p.degreeProd ((j : ℕ) + 1) :=
        Label.snoc_degreeProd_of_le p x (by simp; omega)
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hiii j
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs]; omega
      · rw [hs, hc]; exact h2
      · rw [hd2]; exact h3
      · rw [hs, hc]; exact h4
      · rw [hs, hd1]; exact h5
      · exact (congrArg LabelEntry.PolyOK hs).mpr h6
    · have hir : (i : ℕ) = p.r := by have := i.isLt; simp at this; omega
      have hs : (p.snoc x).entry i.succ = x :=
        Label.snoc_entry_of_eq p x i.succ (by omega)
      have hc : (p.snoc x).entry i.castSucc = p.entry (Fin.last p.r) := by
        rw [Label.snoc_entry_of_lt p x i.castSucc (by omega)]
        congr 1
        ext
        simp only [Fin.val_last]
        omega
      have hd2 : (p.snoc x).degreeProd ((i : ℕ) + 2) = p.d * x.degree := by
        rw [hir]
        exact Label.snoc_degreeProd_succ_succ p x
      have hd1 : (p.snoc x).degreeProd ((i : ℕ) + 1) = p.d := by
        rw [hir, Label.snoc_degreeProd_of_le p x le_rfl, Label.degreeProd_of_le p le_rfl]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs]; omega
      · rw [hs, hc]; omega
      · rw [hd2]; exact hdvd
      · rw [hs, hc, hram, hlev]; rfl
      · rw [hs, hd1]; exact hexp
      · exact (congrArg LabelEntry.PolyOK hs).mpr hpoly

/-- A label of `P^{m+1}_n` with `m + 1 < n` is not an extension by a quadruple of
level `m + 1`. -/
theorem snoc_ne_of_mem_labelSet {m n a b : ℕ} {p p' : Label q}
    (hp : p ∈ labelSet (m + 1) n a b q) {x : LabelEntry q} (hlev : x.level = m + 1) :
    p'.snoc x ≠ p := by
  intro h
  have hlast := lt_level_of_mem_labelSet hp (Fin.last p.r)
  subst h
  have : ((p'.snoc x).entry (Fin.last (p'.snoc x).r)) = x := Label.snoc_entry_last p' x
  rw [this, hlev] at hlast
  omega

end Langlands.BushnellKutzko
