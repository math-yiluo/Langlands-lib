import Langlands.Correspondence.BushnellKutzkoLabelSupports

/-! Extended labels with final ramification index one as ordered supports and polynomial towers. -/

noncomputable section

namespace Langlands.Henniart.LabelCounting

open Langlands.BushnellKutzko Langlands.FieldTheory

private def prefixGcd {t : ℕ} (a : ℕ) (level : Fin t → ℕ) (i : ℕ) : ℕ :=
  Nat.gcd a ((Finset.univ.filter fun j : Fin t => (j : ℕ) < i).gcd level)

private theorem prefixGcd_zero {t : ℕ} (a : ℕ) (level : Fin t → ℕ) :
    prefixGcd a level 0 = a := by
  simp [prefixGcd]

private theorem prefixGcd_full {t : ℕ} (a : ℕ) (level : Fin t → ℕ) :
    prefixGcd a level t = Nat.gcd a (Finset.univ.gcd level) := by
  simp [prefixGcd]

private theorem prefixGcd_succ {t : ℕ} (a : ℕ) (level : Fin t → ℕ) (i : Fin t) :
    prefixGcd a level ((i : ℕ) + 1) = Nat.gcd (level i) (prefixGcd a level i) := by
  unfold prefixGcd
  rw [filter_prefix_succ i, Finset.gcd_insert]
  exact Nat.gcd_left_comm _ _ _

private theorem prefixGcd_one {t : ℕ} (a : ℕ) (level : Fin (t + 1) → ℕ) :
    prefixGcd a level 1 = Nat.gcd (level 0) a := by
  simpa only [Fin.val_zero, prefixGcd_zero] using prefixGcd_succ a level 0

private theorem prefixProd_one {t : ℕ} (d : Fin (t + 1) → ℕ) : prefixProd d 1 = d 0 := by
  simpa only [Fin.val_zero, prefixProd_zero, one_mul] using prefixProd_succ d 0

private theorem entry_ramification_eq {q r a : ℕ} (entry : Fin (r + 1) → LabelEntry q)
    (hfirst : (entry 0).ramification = Nat.gcd (entry 0).level a)
    (hsucc : ∀ i : Fin r, (entry i.succ).ramification =
      Nat.gcd (entry i.succ).level (entry i.castSucc).ramification) (i : Fin (r + 1)) :
    (entry i).ramification = prefixGcd a (fun j => (entry j).level) ((i : ℕ) + 1) := by
  induction i using Fin.induction with
  | zero => exact hfirst.trans (prefixGcd_one a (fun j => (entry j).level)).symm
  | succ i ih =>
    rw [hsucc i, ih]
    exact (prefixGcd_succ a (fun j => (entry j).level) i.succ).symm

private def packPolynomial {q b : ℕ} {D : ℕ+}
    (P : irreduciblePolynomialLabels b (ExtensionField q D)) : FieldPolynomial q :=
  ⟨D, P.val⟩

private theorem packPolynomial_injective {q b : ℕ} (D : ℕ+) :
    Function.Injective (@packPolynomial q b D) := by
  intro P Q h
  exact Subtype.ext (eq_of_heq (FieldPolynomial.mk.inj h).2)

private theorem exists_packPolynomial {q b : ℕ} {D : ℕ+} (w : FieldPolynomial q)
    (hD : w.exponent = D)
    (h : w.poly ∈ irreduciblePolynomialLabels b (ExtensionField q w.exponent)) :
    ∃ P : irreduciblePolynomialLabels b (ExtensionField q D), packPolynomial P = w := by
  subst D
  exact ⟨⟨w.poly, h⟩, rfl⟩

/-- Ordered positive support with a polynomial tower, including the polynomial at level zero. -/
abbrev SupportedTowers (q m a f : ℕ) :=
  Σ r : ℕ, PositiveLevels m a r × PolynomialTowers q (r + 2) f

variable {q m a f r : ℕ}

private def labelOfTower (l : PositiveLevels m a r) {d : DegreeProfile (r + 2) f}
    (P : TowerPolynomials q d) : Label q where
  r := r
  entry i :=
    ⟨packPolynomial (P i.castSucc), l.level i, d.degree i.castSucc,
      prefixGcd a (fun j => (l.level j : ℕ)) ((i : ℕ) + 1)⟩

private theorem labelOfTower_degreeProd (l : PositiveLevels m a r) {d : DegreeProfile (r + 2) f}
    (P : TowerPolynomials q d) {i : ℕ} (hi : i ≤ r + 1) :
    (labelOfTower l P).degreeProd i = prefixProd d.degree i :=
  (prefixProd_castSucc d.degree hi).symm

private theorem label_degreeProd_full (p : Label q) : p.degreeProd (p.r + 1) = p.d :=
  prefixProd_full _

private theorem labelOfTower_d (l : PositiveLevels m a r) {d : DegreeProfile (r + 2) f}
    (P : TowerPolynomials q d) :
    (labelOfTower l P).d = prefixProd d.degree (r + 1) :=
  (label_degreeProd_full _).symm.trans (labelOfTower_degreeProd l P le_rfl)

private theorem labelOfTower_f (l : PositiveLevels m a r) {d : DegreeProfile (r + 2) f}
    (P : TowerPolynomials q d) :
    (labelOfTower l P).f f = d.degree (Fin.last (r + 1)) := by
  have hprod : prefixProd d.degree (r + 1) * d.degree (Fin.last (r + 1)) = f := by
    rw [prefixProd_castSucc d.degree le_rfl, prefixProd_full, ← Fin.prod_univ_castSucc]
    exact d.prod_eq
  unfold Label.f
  rw [labelOfTower_d]
  exact (congrArg (· / prefixProd d.degree (r + 1)) hprod.symm).trans
    (Nat.mul_div_cancel_left _ (prefixProd_pos d.pos _))

private def extendedOfTower (hq : IsPrimePow q) (hm : 0 < m) (ha : 0 < a) (hf : 0 < f)
    (z : SupportedTowers q m a f) : {x ∈ extendedLabelSet m a f q | x.1.e = 1} := by
  obtain ⟨r, l, d, P⟩ := z
  let p := labelOfTower l P
  let j := Fin.last (r + 1)
  refine ⟨(p, packPolynomial (P j)), ⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨hq, hm, ha, hf, fun i => ⟨d.pos i.castSucc, Nat.gcd_pos_of_pos_left _ ha⟩,
      congrArg Fin.val l.top, ?_, ?_, prefixProd_zero _, (P (0 : Fin (r + 1)).castSucc).property,
      ?_⟩
    · change d.degree 0 ∣ f
      rw [← prefixProd_one d.degree]
      exact (prefixProd_dvd d.degree 1).trans d.prod_eq.dvd
    · exact prefixGcd_one a _
    · intro i
      have hi : (i : ℕ) < r := i.isLt
      refine ⟨l.positive i.succ, l.decreasing Fin.castSucc_lt_succ, ?_, ?_, ?_,
        (P i.succ.castSucc).property⟩
      · change p.degreeProd ((i : ℕ) + 2) ∣ f
        rw [labelOfTower_degreeProd l P (show (i : ℕ) + 2 ≤ r + 1 by omega)]
        exact (prefixProd_dvd d.degree _).trans d.prod_eq.dvd
      · exact prefixGcd_succ a _ i.succ
      · exact (labelOfTower_degreeProd l P (show (i : ℕ) + 1 ≤ r + 1 by omega)).symm
  · exact (labelOfTower_d l P).symm
  · change (P j).val ∈ irreduciblePolynomialLabels (p.f f) (ExtensionField q (d.exponent j))
    rw [labelOfTower_f l P]
    exact (P j).property
  · change prefixGcd a (fun i => (l.level i : ℕ)) (r + 1) = 1
    exact (prefixGcd_full a _).trans l.gcd_eq

private theorem extendedOfTower_injective (hq : IsPrimePow q) (hm : 0 < m) (ha : 0 < a)
    (hf : 0 < f) : Function.Injective (extendedOfTower hq hm ha hf) := by
  rintro ⟨r, l, d, P⟩ ⟨r', l', d', P'⟩ h
  have hp : labelOfTower l P = labelOfTower l' P' := congrArg (fun x => x.val.1) h
  have hphi : packPolynomial (P (Fin.last (r + 1))) = packPolynomial (P' (Fin.last (r' + 1))) :=
    congrArg (fun x => x.val.2) h
  have hr : r = r' := congrArg Label.r hp
  subst r'
  have hent : (labelOfTower l P).entry = (labelOfTower l' P').entry :=
    eq_of_heq (Label.mk.inj hp).2
  have hl : l = l' := PositiveLevels.ext (funext fun i => Fin.ext
    (congrArg LabelEntry.level (congrFun hent i)))
  subst l'
  have hd : d = d' := by
    apply DegreeProfile.ext
    funext i
    induction i using Fin.lastCases with
    | last =>
      exact (labelOfTower_f l P).symm.trans
        ((congrArg (fun p : Label q => p.f f) hp).trans (labelOfTower_f l P'))
    | cast i => exact congrArg LabelEntry.degree (congrFun hent i)
  subst d'
  have hP : P = P' := by
    funext i
    apply packPolynomial_injective (d.exponent i)
    induction i using Fin.lastCases with
    | last => exact hphi
    | cast i => exact congrArg LabelEntry.polynomial (congrFun hent i)
  subst P'
  rfl

private theorem extendedOfTower_surjective (hq : IsPrimePow q) (hm : 0 < m) (ha : 0 < a)
    (hf : 0 < f) : Function.Surjective (extendedOfTower hq hm ha hf) := by
  rintro ⟨⟨p, w⟩, ⟨hlabel, hw_exp, hw_mem⟩, he⟩
  obtain ⟨-, -, -, -, hpos, htop, hd0, he0, hD0, hP0, hs⟩ := hlabel
  have hlpos (i : Fin (p.r + 1)) : 0 < (p.entry i).level :=
    Fin.cases (by rw [htop]; exact hm) (fun i => (hs i).1) i
  have hanti : StrictAnti (fun i => (p.entry i).level) :=
    Fin.strictAnti_iff_succ_lt.mpr fun i => (hs i).2.1
  have hle (i : Fin (p.r + 1)) : (p.entry i).level < m + 1 := by
    have h := hanti.antitone (Fin.zero_le i)
    change (p.entry i).level ≤ (p.entry 0).level at h
    rw [htop] at h
    exact Nat.lt_succ_of_le h
  have heram := entry_ramification_eq p.entry he0 (fun i => (hs i).2.2.2.1)
  let l : PositiveLevels m a p.r := {
    level i := ⟨(p.entry i).level, hle i⟩
    top := Fin.ext htop
    positive := hlpos
    decreasing := fun _ _ hij => hanti hij
    gcd_eq := (prefixGcd_full a (fun i => (p.entry i).level)).symm.trans
      ((heram (Fin.last p.r)).symm.trans he) }
  have hdvd (i : Fin (p.r + 1)) : p.degreeProd ((i : ℕ) + 1) ∣ f := by
    induction i using Fin.cases with
    | zero =>
      change prefixProd (fun j => (p.entry j).degree) 1 ∣ f
      rwa [prefixProd_one]
    | succ i => exact (hs i).2.2.1
  have hdiv : p.d ∣ f := by
    have h := hdvd (Fin.last p.r)
    change prefixProd (fun j => (p.entry j).degree) (p.r + 1) ∣ f at h
    rwa [prefixProd_full] at h
  have hdp : 0 < p.d := Finset.prod_pos fun i _ => (hpos i).1
  have hfpos : 0 < p.f f := Nat.div_pos (Nat.le_of_dvd hf hdiv) hdp
  let degrees : Fin (p.r + 2) → ℕ := Fin.snoc (fun i => (p.entry i).degree) (p.f f)
  have hcast (i : Fin (p.r + 1)) : degrees i.castSucc = (p.entry i).degree :=
    Fin.snoc_castSucc (α := fun _ => ℕ) (p.f f) (fun i => (p.entry i).degree) i
  have hlast : degrees (Fin.last (p.r + 1)) = p.f f :=
    Fin.snoc_last (α := fun _ => ℕ) (p.f f) (fun i => (p.entry i).degree)
  let d : DegreeProfile (p.r + 2) f := {
    degree := degrees
    pos i := by
      induction i using Fin.lastCases with
      | last => rw [hlast]; exact hfpos
      | cast i => rw [hcast]; exact (hpos i).1
    prod_eq := by
      rw [Fin.prod_univ_castSucc, hlast]
      simp only [hcast]
      exact Nat.mul_div_cancel' hdiv }
  have hprefix (i : ℕ) (hi : i ≤ p.r + 1) : prefixProd d.degree i = p.degreeProd i :=
    (prefixProd_castSucc d.degree hi).trans
      (congrArg (fun ds => prefixProd ds i) (funext hcast))
  have hslot (i : Fin (p.r + 1)) :
      ((p.entry i).polynomial.exponent : ℕ) = p.degreeProd i ∧
      (p.entry i).polynomial.poly ∈ irreduciblePolynomialLabels (p.entry i).degree
        (ExtensionField q (p.entry i).polynomial.exponent) := by
    induction i using Fin.cases with
    | zero => exact ⟨hD0.trans (prefixProd_zero _).symm, hP0⟩
    | succ i => exact (hs i).2.2.2.2
  let W : Fin (p.r + 2) → FieldPolynomial q :=
    Fin.snoc (fun i => (p.entry i).polynomial) w
  have hW_cast (i : Fin (p.r + 1)) : W i.castSucc = (p.entry i).polynomial :=
    Fin.snoc_castSucc (α := fun _ => FieldPolynomial q) w (fun i => (p.entry i).polynomial) i
  have hW_last : W (Fin.last (p.r + 1)) = w :=
    Fin.snoc_last (α := fun _ => FieldPolynomial q) w (fun i => (p.entry i).polynomial)
  have hW_exp (j : Fin (p.r + 2)) : (W j).exponent = d.exponent j := by
    apply Subtype.ext
    change ((W j).exponent : ℕ) = prefixProd d.degree j
    induction j using Fin.lastCases with
    | last =>
      rwa [Fin.val_last, hprefix _ le_rfl, label_degreeProd_full, hW_last]
    | cast i =>
      rw [Fin.val_castSucc, hprefix _ i.isLt.le]
      simpa only [hW_cast] using (hslot i).1
  have hW_mem (j : Fin (p.r + 2)) :
      (W j).poly ∈ irreduciblePolynomialLabels (d.degree j) (ExtensionField q (W j).exponent) := by
    change (W j).poly ∈ irreduciblePolynomialLabels (degrees j) (ExtensionField q (W j).exponent)
    induction j using Fin.lastCases with
    | last =>
      rw [hlast]
      exact hW_last.symm ▸ hw_mem
    | cast i =>
      rw [hcast]
      exact (hW_cast i).symm ▸ (hslot i).2
  choose P hP using fun j => exists_packPolynomial (W j) (hW_exp j) (hW_mem j)
  have hent (i : Fin (p.r + 1)) : (labelOfTower l P).entry i = p.entry i := by
    have hPi : packPolynomial (P i.castSucc) = (p.entry i).polynomial := by
      simpa only [hW_cast] using hP i.castSucc
    change LabelEntry.mk (packPolynomial (P i.castSucc)) (p.entry i).level
      (degrees i.castSucc) (prefixGcd a (fun j => (p.entry j).level) ((i : ℕ) + 1)) = p.entry i
    rw [hPi, hcast, ← heram]
  have hrec : labelOfTower l P = p := congrArg (Label.mk p.r) (funext hent)
  refine ⟨⟨p.r, l, d, P⟩, Subtype.ext (Prod.ext hrec ?_)⟩
  change packPolynomial (P (Fin.last (p.r + 1))) = w
  simpa only [hW_last] using hP (Fin.last (p.r + 1))

/-- The extended labels of final ramification index one are supported polynomial towers. -/
def extendedLabelsEquiv (hq : IsPrimePow q) (hm : 0 < m) (ha : 0 < a) (hf : 0 < f) :
    {x ∈ extendedLabelSet m a f q | x.1.e = 1} ≃ SupportedTowers q m a f :=
  (Equiv.ofBijective (extendedOfTower hq hm ha hf)
    ⟨extendedOfTower_injective hq hm ha hf, extendedOfTower_surjective hq hm ha hf⟩).symm

end Langlands.Henniart.LabelCounting
