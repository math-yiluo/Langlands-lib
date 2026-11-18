import Langlands.Geometry.FormalGroup.BaseChange
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Finsupp.Weight

/-! # Truncated polynomial test algebras and coordinate maps on nilpotent points -/

noncomputable section

universe v

namespace Langlands.FormalGroup

open CategoryTheory MvPolynomial

section Box

variable (R : Type*) [CommRing R] (σ : Type) (m : ℕ)

/-- Polynomials all of whose coefficients vanish on exponents with every entry below `m`. -/
def boxIdeal : Ideal (MvPolynomial σ R) where
  carrier := {p | ∀ μ : σ →₀ ℕ, (∀ i, μ i < m) → p.coeff μ = 0}
  add_mem' := by
    intro p q hp hq μ hμ
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp μ hμ, hq μ hμ, add_zero]
  zero_mem' := by
    intro μ _
    rfl
  smul_mem' := by
    intro c p hp μ hμ
    classical
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    have hle : ∀ i, x.2 i < m := by
      intro i
      have h := congrArg (fun d : σ →₀ ℕ => d i) hx
      simp only [Finsupp.add_apply] at h
      have := hμ i
      omega
    rw [hp x.2 hle, mul_zero]

/-- The truncated polynomial test algebra. -/
abbrev BoxAlgebra := MvPolynomial σ R ⧸ boxIdeal R σ m

variable {R σ m}

theorem mem_boxIdeal {p : MvPolynomial σ R} :
    p ∈ boxIdeal R σ m ↔ ∀ μ : σ →₀ ℕ, (∀ i, μ i < m) → p.coeff μ = 0 :=
  Iff.rfl

theorem monomial_mem_boxIdeal {μ : σ →₀ ℕ} (hμ : ∃ i, m ≤ μ i) (c : R) :
    monomial μ c ∈ boxIdeal R σ m := by
  classical
  intro ν hν
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · subst h
    obtain ⟨i, hi⟩ := hμ
    exact absurd (hν i) (by omega)
  · rfl

theorem mk_eq_mk_iff_coeff {p q : MvPolynomial σ R} :
    Ideal.Quotient.mk (boxIdeal R σ m) p = Ideal.Quotient.mk (boxIdeal R σ m) q ↔
      ∀ μ : σ →₀ ℕ, (∀ i, μ i < m) → p.coeff μ = q.coeff μ := by
  rw [Ideal.Quotient.eq, mem_boxIdeal]
  refine forall_congr' fun μ => imp_congr_right fun _ => ?_
  rw [MvPolynomial.coeff_sub, sub_eq_zero]

theorem boxIdeal_mono {m m' : ℕ} (h : m ≤ m') : boxIdeal R σ m' ≤ boxIdeal R σ m := by
  intro p hp μ hμ
  exact hp μ fun i => lt_of_lt_of_le (hμ i) h

/-- Monomials of an exponent outside the box vanish on tuples with `m`-th powers zero. -/
theorem prod_pow_eq_zero {T : Type*} [CommRing T] {y : σ → T} (hy : ∀ i, y i ^ m = 0)
    {μ : σ →₀ ℕ} (hμ : ∃ i, m ≤ μ i) : (μ.prod fun i e => y i ^ e) = 0 := by
  obtain ⟨i, hi⟩ := hμ
  by_cases h0 : μ i = 0
  · have hm : m = 0 := by omega
    have h1 : (1 : T) = 0 := by simpa [hm] using hy i
    exact (subsingleton_of_zero_eq_one h1.symm).elim _ _
  · exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr h0)
      (pow_eq_zero_of_le hi (hy i))

/-- Lift the truncated algebra along a tuple whose `m`-th powers vanish. -/
def boxLift {T : Type*} [CommRing T] [Algebra R T] (y : σ → T) (hy : ∀ i, y i ^ m = 0) :
    BoxAlgebra R σ m →ₐ[R] T :=
  Ideal.Quotient.liftₐ (boxIdeal R σ m) (aeval y) (by
    intro p hp
    rw [aeval_eq_eval₂Hom, coe_eval₂Hom, eval₂_eq]
    refine Finset.sum_eq_zero fun μ hμ => ?_
    have hout : ∃ i, m ≤ μ i := by
      by_contra hne
      push Not at hne
      exact (MvPolynomial.mem_support_iff.mp hμ) (hp μ hne)
    have := prod_pow_eq_zero (y := y) hy hout
    rw [Finsupp.prod] at this
    rw [this, mul_zero])

@[simp]
theorem boxLift_mk_X {T : Type*} [CommRing T] [Algebra R T] (y : σ → T)
    (hy : ∀ i, y i ^ m = 0) (i : σ) :
    boxLift y hy (Ideal.Quotient.mk (boxIdeal R σ m) (X i)) = y i := by
  exact aeval_X y i

theorem boxLift_mk {T : Type*} [CommRing T] [Algebra R T] (y : σ → T)
    (hy : ∀ i, y i ^ m = 0) (p : MvPolynomial σ R) :
    boxLift y hy (Ideal.Quotient.mk (boxIdeal R σ m) p) = aeval y p :=
  rfl

theorem aeval_mk_X (p : MvPolynomial σ R) :
    aeval (fun i => Ideal.Quotient.mk (boxIdeal R σ m) (X i)) p =
      Ideal.Quotient.mk (boxIdeal R σ m) p := by
  have h := congrArg (fun φ : MvPolynomial σ R →ₐ[R] BoxAlgebra R σ m => φ p)
    (aeval_unique (Ideal.Quotient.mkₐ R (boxIdeal R σ m)))
  exact h.symm

variable [Finite σ]

variable (σ m) in
/-- The exponents with every entry below `m` form a finite set. -/
theorem boxSet_finite : {μ : σ →₀ ℕ | ∀ i, μ i < m}.Finite := by
  have h : (Set.univ.pi fun _ : σ => Set.Iio m).Finite :=
    Set.Finite.pi fun _ => Set.finite_Iio m
  have h' := h.preimage (f := Finsupp.equivFunOnFinite)
    (Finsupp.equivFunOnFinite.injective.injOn)
  refine h'.subset ?_
  intro μ hμ
  simpa [Set.mem_pi] using hμ

variable (σ m) in
/-- The finite box of exponents with every entry below `m`. -/
def boxFinset : Finset (σ →₀ ℕ) := (boxSet_finite σ m).toFinset

theorem mem_boxFinset {μ : σ →₀ ℕ} : μ ∈ boxFinset σ m ↔ ∀ i, μ i < m := by
  simp [boxFinset]

variable (m) in
/-- Truncate a power series to its coefficients in the box. -/
def truncBox (g : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ μ ∈ boxFinset σ m, monomial μ (MvPowerSeries.coeff μ g)

theorem coeff_truncBox_of_mem (g : MvPowerSeries σ R) {μ : σ →₀ ℕ} (hμ : ∀ i, μ i < m) :
    (truncBox m g).coeff μ = MvPowerSeries.coeff μ g := by
  classical
  rw [truncBox, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_boxFinset.mpr hμ]

theorem aeval_truncBox {T : Type*} [CommRing T] [Algebra R T] (y : σ → T)
    (g : MvPowerSeries σ R) :
    aeval y (truncBox m g) = ∑ μ ∈ boxFinset σ m,
      algebraMap R T (MvPowerSeries.coeff μ g) * μ.prod fun i e => y i ^ e := by
  simp only [truncBox, map_sum, aeval_monomial]

end Box

section Points

variable {R : Type*} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]

omit [Finite σ] in
/-- Points with no formal variables are determined by their constant coefficients. -/
theorem SeriesPoint.ext_constantCoeff {T : Type*} [CommRing T] {x y : SeriesPoint T σ Empty}
    (h : ∀ i, MvPowerSeries.constantCoeff (x.val i) =
      MvPowerSeries.constantCoeff (y.val i)) : x = y := by
  apply SeriesPoint.ext
  intro i
  exact (MvPowerSeries.isEmptyEquiv (σ := Empty) (R := T)).injective (h i)

/-- On a tuple whose `m`-th powers vanish, a formal map is evaluated by its box truncation. -/
theorem constantCoeff_eval_map {T : Type*} [CommRing T] [Algebra R T] {m : ℕ}
    (F : CoordinateMap R σ τ) (x : SeriesPoint T σ Empty)
    (hx : ∀ i, MvPowerSeries.constantCoeff (x.val i) ^ m = 0) (t : τ) :
    MvPowerSeries.constantCoeff ((SeriesPoint.eval (F.map (algebraMap R T)) x).val t) =
      aeval (fun i => MvPowerSeries.constantCoeff (x.val i)) (truncBox m (F.series t)) := by
  rw [SeriesPoint.eval_val, CoordinateMap.map_series,
    MvPowerSeries.constantCoeff_subst x.property, aeval_truncBox]
  rw [finsum_eq_sum_of_support_subset _ (s := boxFinset σ m) ?_]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPowerSeries.coeff_map, smul_eq_mul, map_finsuppProd]
    simp only [map_pow]
  · intro μ hμ
    rw [Function.mem_support] at hμ
    rw [Finset.mem_coe, mem_boxFinset]
    by_contra hne
    push Not at hne
    apply hμ
    rw [map_finsuppProd]
    simp only [map_pow]
    rw [prod_pow_eq_zero hx hne, smul_zero]

omit [Finite σ] in
theorem mk_X_pow_eq_zero (m : ℕ) (i : σ) :
    Ideal.Quotient.mk (boxIdeal R σ m) (X i) ^ m = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, X_pow_eq_monomial]
  exact monomial_mem_boxIdeal ⟨i, by simp⟩ 1

variable (R σ) in
/-- The universal point of the truncated test algebra. -/
def boxPoint (m : ℕ) : SeriesPoint (BoxAlgebra R σ m) σ Empty :=
  ⟨fun i => MvPowerSeries.C (Ideal.Quotient.mk (boxIdeal R σ m) (X i)),
    MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun i => by
      rw [MvPowerSeries.constantCoeff_C]
      exact ⟨m, mk_X_pow_eq_zero m i⟩⟩

@[simp]
theorem constantCoeff_boxPoint (m : ℕ) (i : σ) :
    MvPowerSeries.constantCoeff ((boxPoint R σ m).val i) =
      Ideal.Quotient.mk (boxIdeal R σ m) (X i) :=
  MvPowerSeries.constantCoeff_C _

/-- Every tuple whose `m`-th powers vanish is pulled back from the universal box point. -/
theorem boxPoint_map_boxLift {T : Type*} [CommRing T] [Algebra R T] {m : ℕ}
    (x : SeriesPoint T σ Empty)
    (hx : ∀ i, MvPowerSeries.constantCoeff (x.val i) ^ m = 0) :
    (boxPoint R σ m).map (boxLift _ hx).toRingHom = x := by
  apply SeriesPoint.ext_constantCoeff
  intro i
  rw [SeriesPoint.map_val, MvPowerSeries.constantCoeff_map, constantCoeff_boxPoint]
  exact boxLift_mk_X _ hx i

theorem boxPoint_map_factor {m m' : ℕ} (h : m ≤ m') :
    (boxPoint R σ m').map (Ideal.Quotient.factorₐ R (boxIdeal_mono (R := R) (σ := σ) h)).toRingHom =
      boxPoint R σ m := by
  apply SeriesPoint.ext_constantCoeff
  intro i
  rw [SeriesPoint.map_val, MvPowerSeries.constantCoeff_map, constantCoeff_boxPoint,
    constantCoeff_boxPoint]
  rfl

theorem boxPoint_one : boxPoint R σ 1 = SeriesPoint.zero := by
  apply SeriesPoint.ext_constantCoeff
  intro i
  rw [constantCoeff_boxPoint, SeriesPoint.zero_val, map_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact monomial_mem_boxIdeal (μ := Finsupp.single i 1) ⟨i, by simp⟩ 1

/-- Some common power kills every coordinate of a point. -/
theorem exists_pow_eq_zero {T : Type*} [CommRing T] (x : SeriesPoint T σ Empty) :
    ∃ m : ℕ, ∀ i, MvPowerSeries.constantCoeff (x.val i) ^ m = 0 := by
  have hn : ∀ i, ∃ n : ℕ, MvPowerSeries.constantCoeff (x.val i) ^ n = 0 :=
    fun i => x.property.const_coeff i
  choose n hn using hn
  have := Fintype.ofFinite σ
  refine ⟨Finset.univ.sup n, fun i => pow_eq_zero_of_le ?_ (hn i)⟩
  exact Finset.le_sup (Finset.mem_univ i)

end Points

end Langlands.FormalGroup
