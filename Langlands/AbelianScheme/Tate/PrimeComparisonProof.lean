import Langlands.AbelianScheme.Tate.PrimeComparisonStatement
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Int.GCD

set_option maxHeartbeats 800000

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeComparison
open Langlands.TateTwist.Divisibility (AwayPrime)
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
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
    (hab : a.Coprime b) {x y : Level G T (a * b)}
    (h₁ : transition G T (dvd_mul_right a b) x = transition G T (dvd_mul_right a b) y)
    (h₂ : transition G T (dvd_mul_left b a) x = transition G T (dvd_mul_left b a) y) : x = y := by
  apply toSection_injective G T (a * b)
  apply sub_eq_zero.mp
  apply (nsmul_eq_zero_iff_of_coprime hab).mp
  constructor
  · have h := congrArg (toSection G T b) h₂
    change ((a * b) / b) • toSection G T (a * b) x = ((a * b) / b) • toSection G T (a * b) y at h
    rw [Nat.mul_div_cancel _ hb] at h
    simpa [nsmul_sub] using sub_eq_zero.mpr h
  · have h := congrArg (toSection G T a) h₁
    change ((a * b) / a) • toSection G T (a * b) x = ((a * b) / a) • toSection G T (a * b) y at h
    rw [Nat.mul_div_cancel_left _ ha] at h
    simpa [nsmul_sub] using sub_eq_zero.mpr h

private lemma coprime_transition_surjective {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (x : Level G T a) (y : Level G T b) :
    ∃ z : Level G T (a * b), transition G T (dvd_mul_right a b) z = x ∧
      transition G T (dvd_mul_left b a) z = y := by
  obtain ⟨z, hz, hx, hy⟩ := bezout_reconstruct hab (toSection G T a x) (toSection G T b y)
    (by rw [← map_nsmul, level_nsmul_eq_zero, map_zero])
    (by rw [← map_nsmul, level_nsmul_eq_zero, map_zero])
  let w : Level G T (a * b) := Additive.ofMul ⟨Additive.toMul z, (mem_levelGroup G T (a * b) _).mpr hz⟩
  refine ⟨w, ?_, ?_⟩
  · apply toSection_injective G T a
    change Additive.ofMul (Additive.toMul z ^ ((a * b) / a)) = toSection G T a x
    rw [Nat.mul_div_cancel_left _ ha]
    exact hx
  · apply toSection_injective G T b
    change Additive.ofMul (Additive.toMul z ^ ((a * b) / b)) = toSection G T b y
    rw [Nat.mul_div_cancel _ hb]
    exact hy

private lemma level_prime_ext : ∀ n : ℕ, 0 < n → ∀ x y : Level G T n,
    (∀ (p : Nat.Primes) (k : ℕ) (h : (p : ℕ) ^ k ∣ n),
      transition G T h x = transition G T h y) → x = y := by
  apply Nat.recOnPrimeCoprime
  · intro h; exact (Nat.lt_irrefl 0 h).elim
  · intro p k hp hn x y h
    simpa only [transition_self G T hn] using h ⟨p, hp⟩ k (dvd_refl _)
  · intro a b ha hb hab iha ihb hn x y h
    apply coprime_transition_injective G T (by omega) (by omega) hab
    · apply iha (by omega)
      intro p k hd
      simpa only [transition_comp] using h p k (hd.trans (dvd_mul_right a b))
    · apply ihb (by omega)
      intro p k hd
      simpa only [transition_comp] using h p k (hd.trans (dvd_mul_left b a))

private lemma prime_transition_le (p : Nat.Primes) {a b : ℕ} (h : a ≤ b)
    (x : PrimeAdic.Integral G T (p : ℕ)) :
    transition G T (pow_dvd_pow (p : ℕ) h) (x.val b) = x.val a := by
  induction b, h using Nat.le_induction with
  | base => exact transition_self G T (pow_pos p.property.pos a) _
  | succ b h ih =>
    rw [← transition_comp G T (pow_dvd_pow (p : ℕ) h)
      (pow_dvd_pow (p : ℕ) (Nat.le_succ b)), x.property b]
    exact ih

private lemma level_one_ext (x y : Level G T 1) : x = y := by
  have hx := level_nsmul_eq_zero G T 1 x
  have hy := level_nsmul_eq_zero G T 1 y
  simpa only [one_nsmul] using hx.trans hy.symm

private def coprimeJoin {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (x : Level G T a × Level G T b) : Level G T (a * b) :=
  (coprime_transition_surjective G T ha hb hab x.1 x.2).choose

private lemma coprimeJoin_spec {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (x : Level G T a × Level G T b) :
    transition G T (dvd_mul_right a b) (coprimeJoin G T ha hb hab x) = x.1 ∧
    transition G T (dvd_mul_left b a) (coprimeJoin G T ha hb hab x) = x.2 :=
  (coprime_transition_surjective G T ha hb hab x.1 x.2).choose_spec

private lemma exists_continuous_coordinate : ∀ n : ℕ, 0 < n →
    ∃ f : PrimeProduct G T → Level G T n, Continuous f ∧
      ∀ (x : PrimeProduct G T) (p : Nat.Primes) (k : ℕ) (h : (p : ℕ) ^ k ∣ n),
        transition G T h (f x) = (x p).val k := by
  apply Nat.recOnPrimeCoprime
  · intro h; exact (Nat.lt_irrefl 0 h).elim
  · intro p e hp hn
    let : Fact p.Prime := ⟨hp⟩
    let q : Nat.Primes := ⟨p, hp⟩
    refine ⟨fun x => (x q).val e,
      (PrimeAdic.continuous_evaluation G T p e).comp (continuous_apply q), ?_⟩
    intro x r k h
    by_cases hk : k = 0
    · subst k
      exact level_one_ext G T _ _
    · have hrp : (r : ℕ) = p := by
        apply (Nat.dvd_prime hp).mp _ |>.resolve_left r.property.ne_one
        exact r.property.dvd_of_dvd_pow (dvd_trans (dvd_pow_self _ hk) h)
      have hrq : r = q := Subtype.ext hrp
      subst r
      exact prime_transition_le G T q ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h) _
  · intro a b ha hb hab iha ihb hn
    obtain ⟨f, hf, hfs⟩ := iha (by omega)
    obtain ⟨g, hg, hgs⟩ := ihb (by omega)
    refine ⟨fun x => coprimeJoin G T (by omega) (by omega) hab (f x, g x),
      (continuous_of_discreteTopology (f := coprimeJoin G T (by omega) (by omega) hab)).comp
        (hf.prodMk hg), ?_⟩
    intro x p k h
    by_cases hk : k = 0
    · subst k; exact level_one_ext G T _ _
    · have hpp : IsPrimePow ((p : ℕ) ^ k) :=
        (isPrimePow_nat_iff _).mpr ⟨p, k, p.property, Nat.pos_of_ne_zero hk, rfl⟩
      rcases (hab.isPrimePow_dvd_mul hpp).mp h with hd | hd
      · rw [← transition_comp G T hd (dvd_mul_right a b),
          (coprimeJoin_spec G T (by omega) (by omega) hab (f x, g x)).1]
        exact hfs x p k hd
      · rw [← transition_comp G T hd (dvd_mul_left b a),
          (coprimeJoin_spec G T (by omega) (by omega) hab (f x, g x)).2]
        exact hgs x p k hd

private def reconstructedCoordinate (n : ℕ) (hn : 0 < n) : PrimeProduct G T → Level G T n :=
  (exists_continuous_coordinate G T n hn).choose

private lemma continuous_reconstructedCoordinate (n : ℕ) (hn : 0 < n) :
    Continuous (reconstructedCoordinate G T n hn) :=
  (exists_continuous_coordinate G T n hn).choose_spec.1

private lemma reconstructedCoordinate_spec (n : ℕ) (hn : 0 < n) (x : PrimeProduct G T)
    (p : Nat.Primes) (k : ℕ) (h : (p : ℕ) ^ k ∣ n) :
    transition G T h (reconstructedCoordinate G T n hn x) = (x p).val k :=
  (exists_continuous_coordinate G T n hn).choose_spec.2 x p k h

private def fromPrimeProduct (x : PrimeProduct G T) : Full G T :=
  ⟨fun n => reconstructedCoordinate G T n.val n.property.1 x, by
    intro n m h
    apply level_prime_ext G T n.val n.property.1
    intro p k hd
    rw [transition_comp, reconstructedCoordinate_spec, reconstructedCoordinate_spec]⟩

private lemma continuous_fromPrimeProduct : Continuous (fromPrimeProduct G T) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun (n : Index (fun _ => True)) =>
    continuous_reconstructedCoordinate G T n.val n.property.1)

private lemma toPrimeProduct_fromPrimeProduct (x : PrimeProduct G T) :
    toPrimeProduct G T (fromPrimeProduct G T x) = x := by
  funext p
  apply Subtype.ext
  funext k
  exact (transition_self G T (pow_pos p.property.pos k) _).symm.trans
    (reconstructedCoordinate_spec G T _ (pow_pos p.property.pos k) x p k (dvd_refl _))

private lemma toPrimeProduct_injective : Function.Injective (toPrimeProduct G T) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  apply level_prime_ext G T n.val n.property.1
  intro p k hd
  have he := congrArg (fun z : PrimeProduct G T => (z p).val k) hxy
  let i : Index (fun _ => True) := ⟨(p : ℕ) ^ k, pow_pos p.property.pos k, trivial⟩
  change x.val i = y.val i at he
  exact (x.property i n hd).trans (he.trans (y.property i n hd).symm)

private def fullPrimeEquiv : Full G T ≃+ PrimeProduct G T :=
  { toPrimeProduct G T with
    invFun := fromPrimeProduct G T
    left_inv := fun _ => toPrimeProduct_injective G T (toPrimeProduct_fromPrimeProduct G T _)
    right_inv := toPrimeProduct_fromPrimeProduct G T }

/-- The canonical comparison on the full actual torsion-section limit is a topological additive equivalence. -/
theorem fullPrimeProductComparison : FullPrimeProductComparison G T :=
  ⟨fullPrimeEquiv G T, rfl, continuous_toPrimeProduct G T, continuous_fromPrimeProduct G T⟩

private def extendAwayPrimeProduct (m : ℕ) (x : AwayPrimeProduct G T m) : PrimeProduct G T := by
  classical
  exact fun p => if h : Nat.Coprime (p : ℕ) m then x ⟨p, h⟩ else 0

private lemma continuous_extendAwayPrimeProduct (m : ℕ) :
    Continuous (extendAwayPrimeProduct G T m) := by
  classical
  apply continuous_pi
  intro p
  by_cases h : Nat.Coprime (p : ℕ) m
  · simpa only [extendAwayPrimeProduct, dite_eq_left h] using
      (continuous_apply (⟨p, h⟩ : AwayPrime m))
  · simp only [extendAwayPrimeProduct, dite_eq_right h]
    exact continuous_const

private lemma toAwayPrimeProduct_injective (m : ℕ) :
    Function.Injective (toAwayPrimeProduct G T m) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  apply level_prime_ext G T n.val n.property.1
  intro p k hd
  by_cases hk : k = 0
  · subst k; exact level_one_ext G T _ _
  · have hp : Nat.Coprime (p : ℕ) m :=
      n.property.2.of_dvd_left ((dvd_pow_self (p : ℕ) hk).trans hd)
    have he := congrArg (fun z : AwayPrimeProduct G T m => (z ⟨p, hp⟩).val k) hxy
    let i : Index (fun a => Nat.Coprime a m) :=
      ⟨(p : ℕ) ^ k, pow_pos p.property.pos k, hp.pow_left k⟩
    change x.val i = y.val i at he
    exact (x.property i n hd).trans (he.trans (y.property i n hd).symm)

private def fromAwayPrimeProduct (m : ℕ) (x : AwayPrimeProduct G T m) : Away G T m :=
  restrictAway G T m (fromPrimeProduct G T (extendAwayPrimeProduct G T m x))

private lemma continuous_fromAwayPrimeProduct (m : ℕ) :
    Continuous (fromAwayPrimeProduct G T m) :=
  (continuous_restrictAway G T m).comp
    ((continuous_fromPrimeProduct G T).comp (continuous_extendAwayPrimeProduct G T m))

private lemma toAwayPrimeProduct_fromAwayPrimeProduct (m : ℕ) (x : AwayPrimeProduct G T m) :
    toAwayPrimeProduct G T m (fromAwayPrimeProduct G T m x) = x := by
  classical
  rw [fromAwayPrimeProduct, toPrimeProduct_restrictAway, toPrimeProduct_fromPrimeProduct]
  funext p
  exact dite_eq_left p.property

private def awayPrimeEquiv (m : ℕ) : Away G T m ≃+ AwayPrimeProduct G T m :=
  { toAwayPrimeProduct G T m with
    invFun := fromAwayPrimeProduct G T m
    left_inv := fun _ => toAwayPrimeProduct_injective G T m
      (toAwayPrimeProduct_fromAwayPrimeProduct G T m _)
    right_inv := toAwayPrimeProduct_fromAwayPrimeProduct G T m }

/-- The canonical away comparison is valid for every natural excluded modulus. -/
theorem awayPrimeProductComparison (m : ℕ) : AwayPrimeProductComparison G T m :=
  ⟨awayPrimeEquiv G T m, rfl, continuous_toAwayPrimeProduct G T m,
    continuous_fromAwayPrimeProduct G T m⟩

/-- Full and away prime-product decompositions of the actual torsion-section limits. -/
theorem primeProductComparisons : PrimeProductComparisons G T :=
  ⟨fullPrimeProductComparison G T, awayPrimeProductComparison G T⟩

end Langlands.GroupScheme.Tate.PrimeComparison
