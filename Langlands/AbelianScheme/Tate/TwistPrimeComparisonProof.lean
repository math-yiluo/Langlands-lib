import Langlands.AbelianScheme.Tate.TwistPrimeComparisonStatement
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Int.GCD

noncomputable section
namespace Langlands.TateTwist.Divisibility
universe u
variable (R : Type u) [CommRing R]
local instance proofPrimeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

private lemma bezout_reconstruct {A : Type*} [AddCommGroup A] {a b : ℕ}
    (hab : a.Coprime b) (x y : A) (hx : a • x = 0) (hy : b • y = 0) :
    ∃ z : A, (a * b) • z = 0 ∧ b • z = x ∧ a • z = y := by
  have hbez : (a : ℤ) * a.gcdA b + (b : ℤ) * a.gcdB b = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hab.gcd_eq_one]; rfl
  have hx' : ((b : ℤ) * a.gcdB b) • x = x := by
    have h := congrArg (fun z : ℤ => z • x) hbez
    simpa only [add_zsmul, mul_zsmul, natCast_zsmul,
      smul_comm a (a.gcdA b), hx, smul_zero, zero_add, one_zsmul] using h
  have hy' : ((a : ℤ) * a.gcdA b) • y = y := by
    have h := congrArg (fun z : ℤ => z • y) hbez
    simpa only [add_zsmul, mul_zsmul, natCast_zsmul,
      smul_comm b (a.gcdB b), hy, smul_zero, add_zero, one_zsmul] using h
  let z := a.gcdB b • x + a.gcdA b • y
  have hzx : b • z = x := by
    change b • (a.gcdB b • x + a.gcdA b • y) = x
    rw [nsmul_add, smul_comm b (a.gcdA b), hy, smul_zero, add_zero]
    simpa only [mul_zsmul, natCast_zsmul] using hx'
  have hzy : a • z = y := by
    change a • (a.gcdB b • x + a.gcdA b • y) = y
    rw [nsmul_add, smul_comm a (a.gcdB b), hx, smul_zero, zero_add]
    simpa only [mul_zsmul, natCast_zsmul] using hy'
  exact ⟨z, by rw [mul_smul, hzx, hx], hzx, hzy⟩

private lemma coprime_transition_injective {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) {x y : Level R (a * b)}
    (h₁ : transition R (dvd_mul_right a b) x = transition R (dvd_mul_right a b) y)
    (h₂ : transition R (dvd_mul_left b a) x = transition R (dvd_mul_left b a) y) : x = y := by
  apply toUnit_injective R (a * b)
  apply sub_eq_zero.mp
  apply (nsmul_eq_zero_iff_of_coprime hab).mp
  constructor
  · have h := congrArg (toUnit R b) h₂
    change ((a * b) / b) • toUnit R (a * b) x = ((a * b) / b) • toUnit R (a * b) y at h
    rw [Nat.mul_div_cancel _ hb] at h
    simpa [nsmul_sub] using sub_eq_zero.mpr h
  · have h := congrArg (toUnit R a) h₁
    change ((a * b) / a) • toUnit R (a * b) x = ((a * b) / a) • toUnit R (a * b) y at h
    rw [Nat.mul_div_cancel_left _ ha] at h
    simpa [nsmul_sub] using sub_eq_zero.mpr h

private lemma coprime_transition_surjective {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (x : Level R a) (y : Level R b) :
    ∃ z : Level R (a * b), transition R (dvd_mul_right a b) z = x ∧
      transition R (dvd_mul_left b a) z = y := by
  obtain ⟨z, hz, hx, hy⟩ := bezout_reconstruct hab (toUnit R a x) (toUnit R b y)
    (by rw [← map_nsmul, level_nsmul_eq_zero, map_zero])
    (by rw [← map_nsmul, level_nsmul_eq_zero, map_zero])
  let w : Level R (a * b) := Additive.ofMul ⟨Additive.toMul z, hz⟩
  refine ⟨w, ?_, ?_⟩
  · apply toUnit_injective R a
    change Additive.ofMul (Additive.toMul z ^ ((a * b) / a)) = toUnit R a x
    rw [Nat.mul_div_cancel_left _ ha]
    exact hx
  · apply toUnit_injective R b
    change Additive.ofMul (Additive.toMul z ^ ((a * b) / b)) = toUnit R b y
    rw [Nat.mul_div_cancel _ hb]
    exact hy

private lemma level_prime_ext : ∀ n : ℕ, 0 < n → ∀ x y : Level R n,
    (∀ (p : Nat.Primes) (k : ℕ) (h : (p : ℕ) ^ k ∣ n),
      transition R h x = transition R h y) → x = y := by
  apply Nat.recOnPrimeCoprime
  · intro h; exact (Nat.lt_irrefl 0 h).elim
  · intro p k hp hn x y h
    simpa only [transition_self R hn] using h ⟨p, hp⟩ k (dvd_refl _)
  · intro a b ha hb hab iha ihb hn x y h
    apply coprime_transition_injective R (by omega) (by omega) hab
    · apply iha (by omega)
      intro p k hd
      simpa only [transition_comp] using h p k (hd.trans (dvd_mul_right a b))
    · apply ihb (by omega)
      intro p k hd
      simpa only [transition_comp] using h p k (hd.trans (dvd_mul_left b a))

private lemma prime_transition_le (p : Nat.Primes) {a b : ℕ} (h : a ≤ b)
    (x : TateTwist.Integral R (p : ℕ)) :
    transition R (pow_dvd_pow (p : ℕ) h) (x.val b) = x.val a := by
  induction b, h using Nat.le_induction with
  | base => exact transition_self R (pow_pos p.property.pos a) _
  | succ b h ih =>
    rw [← transition_comp R (pow_dvd_pow (p : ℕ) h)
      (pow_dvd_pow (p : ℕ) (Nat.le_succ b)), x.property b]
    exact ih

private lemma level_one_ext (x y : Level R 1) : x = y := by
  have hx := level_nsmul_eq_zero R 1 x
  have hy := level_nsmul_eq_zero R 1 y
  simpa only [one_nsmul] using hx.trans hy.symm

private def coprimeJoin {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (x : Level R a × Level R b) : Level R (a * b) :=
  (coprime_transition_surjective R ha hb hab x.1 x.2).choose

private lemma coprimeJoin_spec {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (x : Level R a × Level R b) :
    transition R (dvd_mul_right a b) (coprimeJoin R ha hb hab x) = x.1 ∧
    transition R (dvd_mul_left b a) (coprimeJoin R ha hb hab x) = x.2 :=
  (coprime_transition_surjective R ha hb hab x.1 x.2).choose_spec

private lemma exists_continuous_coordinate : ∀ n : ℕ, 0 < n →
    ∃ f : PrimeProduct R → Level R n, Continuous f ∧
      ∀ (x : PrimeProduct R) (p : Nat.Primes) (k : ℕ) (h : (p : ℕ) ^ k ∣ n),
        transition R h (f x) = (x p).val k := by
  apply Nat.recOnPrimeCoprime
  · intro h; exact (Nat.lt_irrefl 0 h).elim
  · intro p e hp hn
    let : Fact p.Prime := ⟨hp⟩
    let q : Nat.Primes := ⟨p, hp⟩
    refine ⟨fun x => (x q).val e,
      (TateTwist.continuous_evaluation R p e).comp (continuous_apply q), ?_⟩
    intro x r k h
    by_cases hk : k = 0
    · subst k
      exact level_one_ext R _ _
    · have hrp : (r : ℕ) = p := by
        apply (Nat.dvd_prime hp).mp _ |>.resolve_left r.property.ne_one
        exact r.property.dvd_of_dvd_pow (dvd_trans (dvd_pow_self _ hk) h)
      have hrq : r = q := Subtype.ext hrp
      subst r
      exact prime_transition_le R q ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h) _
  · intro a b ha hb hab iha ihb hn
    obtain ⟨f, hf, hfs⟩ := iha (by omega)
    obtain ⟨g, hg, hgs⟩ := ihb (by omega)
    refine ⟨fun x => coprimeJoin R (by omega) (by omega) hab (f x, g x),
      (continuous_of_discreteTopology (f := coprimeJoin R (by omega) (by omega) hab)).comp
        (hf.prodMk hg), ?_⟩
    intro x p k h
    by_cases hk : k = 0
    · subst k; exact level_one_ext R _ _
    · have hpp : IsPrimePow ((p : ℕ) ^ k) :=
        (isPrimePow_nat_iff _).mpr ⟨p, k, p.property, Nat.pos_of_ne_zero hk, rfl⟩
      rcases (hab.isPrimePow_dvd_mul hpp).mp h with hd | hd
      · rw [← transition_comp R hd (dvd_mul_right a b),
          (coprimeJoin_spec R (by omega) (by omega) hab (f x, g x)).1]
        exact hfs x p k hd
      · rw [← transition_comp R hd (dvd_mul_left b a),
          (coprimeJoin_spec R (by omega) (by omega) hab (f x, g x)).2]
        exact hgs x p k hd

private def reconstructedCoordinate (n : ℕ) (hn : 0 < n) : PrimeProduct R → Level R n :=
  (exists_continuous_coordinate R n hn).choose

private lemma continuous_reconstructedCoordinate (n : ℕ) (hn : 0 < n) :
    Continuous (reconstructedCoordinate R n hn) :=
  (exists_continuous_coordinate R n hn).choose_spec.1

private lemma reconstructedCoordinate_spec (n : ℕ) (hn : 0 < n) (x : PrimeProduct R)
    (p : Nat.Primes) (k : ℕ) (h : (p : ℕ) ^ k ∣ n) :
    transition R h (reconstructedCoordinate R n hn x) = (x p).val k :=
  (exists_continuous_coordinate R n hn).choose_spec.2 x p k h

private def fromPrimeProduct (x : PrimeProduct R) : Full R :=
  ⟨fun n => reconstructedCoordinate R n.val n.property.1 x, by
    intro n m h
    apply level_prime_ext R n.val n.property.1
    intro p k hd
    rw [transition_comp, reconstructedCoordinate_spec, reconstructedCoordinate_spec]⟩

private lemma continuous_fromPrimeProduct : Continuous (fromPrimeProduct R) :=
  (continuous_pi (fun n => continuous_reconstructedCoordinate R n.val n.property.1)).subtype_mk _

private lemma toPrimeProduct_fromPrimeProduct (x : PrimeProduct R) :
    toPrimeProduct R (fromPrimeProduct R x) = x := by
  funext p
  apply Subtype.ext
  funext k
  exact (transition_self R (pow_pos p.property.pos k) _).symm.trans
    (reconstructedCoordinate_spec R _ (pow_pos p.property.pos k) x p k (dvd_refl _))

private lemma toPrimeProduct_injective : Function.Injective (toPrimeProduct R) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  apply level_prime_ext R n.val n.property.1
  intro p k hd
  have he := congrArg (fun z : PrimeProduct R => (z p).val k) hxy
  exact (x.property _ n hd).trans (he.trans (y.property _ n hd).symm)

private def fullPrimeEquiv : Full R ≃+ PrimeProduct R :=
  { toPrimeProduct R with
    invFun := fromPrimeProduct R
    left_inv := fun _ => toPrimeProduct_injective R (toPrimeProduct_fromPrimeProduct R _)
    right_inv := toPrimeProduct_fromPrimeProduct R }

/-- The canonical comparison on the full root limit is a topological additive equivalence. -/
theorem fullPrimeProductComparison : FullPrimeProductComparison R :=
  ⟨fullPrimeEquiv R, rfl, continuous_toPrimeProduct R, continuous_fromPrimeProduct R⟩

private def extendAwayPrimeProduct (m : ℕ) (x : AwayPrimeProduct R m) : PrimeProduct R := by
  classical
  exact fun p => if h : Nat.Coprime (p : ℕ) m then x ⟨p, h⟩ else 0

private lemma continuous_extendAwayPrimeProduct (m : ℕ) :
    Continuous (extendAwayPrimeProduct R m) := by
  classical
  apply continuous_pi
  intro p
  by_cases h : Nat.Coprime (p : ℕ) m
  · simpa only [extendAwayPrimeProduct, dite_eq_left h] using
      (continuous_apply (⟨p, h⟩ : AwayPrime m))
  · simp only [extendAwayPrimeProduct, dite_eq_right h]
    exact continuous_const

private lemma toAwayPrimeProduct_injective (m : ℕ) :
    Function.Injective (toAwayPrimeProduct R m) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  apply level_prime_ext R n.val n.property.1
  intro p k hd
  by_cases hk : k = 0
  · subst k; exact level_one_ext R _ _
  · have hp : Nat.Coprime (p : ℕ) m :=
      n.property.2.of_dvd_left ((dvd_pow_self (p : ℕ) hk).trans hd)
    have he := congrArg (fun z : AwayPrimeProduct R m => (z ⟨p, hp⟩).val k) hxy
    exact (x.property _ n hd).trans (he.trans (y.property _ n hd).symm)

private def fromAwayPrimeProduct (m : ℕ) (x : AwayPrimeProduct R m) : Away R m :=
  restrictAway R m (fromPrimeProduct R (extendAwayPrimeProduct R m x))

private lemma continuous_fromAwayPrimeProduct (m : ℕ) :
    Continuous (fromAwayPrimeProduct R m) :=
  (continuous_restrictAway R m).comp
    ((continuous_fromPrimeProduct R).comp (continuous_extendAwayPrimeProduct R m))

private lemma toAwayPrimeProduct_fromAwayPrimeProduct (m : ℕ) (x : AwayPrimeProduct R m) :
    toAwayPrimeProduct R m (fromAwayPrimeProduct R m x) = x := by
  classical
  rw [fromAwayPrimeProduct, toPrimeProduct_restrictAway, toPrimeProduct_fromPrimeProduct]
  funext p
  exact dite_eq_left p.property

private def awayPrimeEquiv (m : ℕ) : Away R m ≃+ AwayPrimeProduct R m :=
  { toAwayPrimeProduct R m with
    invFun := fromAwayPrimeProduct R m
    left_inv := fun _ => toAwayPrimeProduct_injective R m
      (toAwayPrimeProduct_fromAwayPrimeProduct R m _)
    right_inv := toAwayPrimeProduct_fromAwayPrimeProduct R m }

/-- The canonical away comparison is valid for every natural excluded modulus. -/
theorem awayPrimeProductComparison (m : ℕ) : AwayPrimeProductComparison R m :=
  ⟨awayPrimeEquiv R m, rfl, continuous_toAwayPrimeProduct R m,
    continuous_fromAwayPrimeProduct R m⟩

/-- Full and away prime-product decompositions of the actual roots-of-unity limits. -/
theorem primeProductComparisons : PrimeProductComparisons R :=
  ⟨fullPrimeProductComparison R, awayPrimeProductComparison R⟩

end Langlands.TateTwist.Divisibility
