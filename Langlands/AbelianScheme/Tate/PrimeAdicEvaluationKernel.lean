import Langlands.AbelianScheme.Tate.PrimeAdicSeparation

/-! # The kernel of evaluation on the prime-adic Tate module

An element of the actual integral `p`-adic Tate module whose level-`p ^ N` coordinate
vanishes is `p ^ N` times another element.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeAdic

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
  (p : ℕ) [Fact p.Prime]

/-- Iterated transitions: the section at level `p ^ n` is `p ^ m` times the section at
level `p ^ (n + m)`. -/
theorem toSection_evaluation_add (x : Integral G T p) (n m : ℕ) :
    toSection G T (p ^ n) (evaluation G T p n x) =
      p ^ m • toSection G T (p ^ (n + m)) (evaluation G T p (n + m) x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, ← evaluation_transition G T p (n + m) x, toSection_transition_succ, smul_smul,
      ← pow_succ]
    rfl

/-- The section of a coordinate depends only on the index. -/
theorem toSection_evaluation_congr (x : Integral G T p) {a b : ℕ} (h : a = b) :
    toSection G T (p ^ a) (evaluation G T p a x) =
      toSection G T (p ^ b) (evaluation G T p b x) := by
  subst h
  rfl

/-- An element with vanishing level-`p ^ N` coordinate is divisible by `p ^ N`. -/
theorem exists_smul_eq_of_evaluation_eq_zero (x : Integral G T p) (N : ℕ)
    (hx : evaluation G T p N x = 0) :
    ∃ y : Integral G T p, ((p ^ N : ℕ) : ℤ_[p]) • y = x := by
  have hmem : ∀ i, Additive.toMul (toSection G T (p ^ (N + i))
      (evaluation G T p (N + i) x)) ∈ levelGroup G T (p ^ i) := by
    intro i
    rw [mem_levelGroup]
    have h := toSection_evaluation_add G T p x N i
    rw [hx, map_zero] at h
    have h' := congrArg Additive.toMul h
    rw [toMul_nsmul] at h'
    exact h'.symm
  let yv : ∀ i, Level G T (p ^ i) := fun i => Additive.ofMul ⟨_, hmem i⟩
  have hyv : ∀ i, toSection G T (p ^ i) (yv i) =
      toSection G T (p ^ (N + i)) (evaluation G T p (N + i) x) := fun i => rfl
  have hcoh : yv ∈ coherent G T p := by
    intro i
    apply toSection_injective G T (p ^ i)
    rw [toSection_transition_succ, hyv, hyv]
    have h := toSection_evaluation_add G T p x (N + i) 1
    rw [pow_one] at h
    rw [h]
    rfl
  let y : Integral G T p := ⟨yv, hcoh⟩
  have hy : ∀ i, evaluation G T p i y = yv i := fun i => rfl
  refine ⟨y, ?_⟩
  apply Subtype.ext
  funext i
  apply toSection_injective G T (p ^ i)
  change toSection G T (p ^ i) (evaluation G T p i (((p ^ N : ℕ) : ℤ_[p]) • y)) =
    toSection G T (p ^ i) (evaluation G T p i x)
  rw [evaluation_natCast_smul, map_nsmul, toSection_evaluation_add G T p x i N, hy, hyv,
    toSection_evaluation_congr G T p x (Nat.add_comm N i)]

variable {G}

/-- If evaluation at level `p ^ N` is surjective and every `p ^ N`-multiple lies in the image
of the Tate map of `f`, then the cokernels of the Tate map and of the level map at `p ^ N`
have the same cardinality. -/
theorem card_quotient_range_map_eq (f : G ⟶ G) (N : ℕ)
    (hsurj : Function.Surjective (evaluation G T p N))
    (hdiv : ∀ m : Integral G T p, ((p ^ N : ℕ) : ℤ_[p]) • m ∈ LinearMap.range (map T p f)) :
    Nat.card (Integral G T p ⧸ LinearMap.range (map T p f)) =
      Nat.card (Level G T (p ^ N) ⧸ (levelMap T f (p ^ N)).range) := by
  let π : Integral G T p →+ Level G T (p ^ N) ⧸ (levelMap T f (p ^ N)).range :=
    (QuotientAddGroup.mk' _).comp (evaluation G T p N).toAddMonoidHom
  have hπsurj : Function.Surjective π := (QuotientAddGroup.mk'_surjective _).comp hsurj
  have hker : π.ker = (LinearMap.range (map T p f)).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
    change (QuotientAddGroup.mk (evaluation G T p N x) :
      Level G T (p ^ N) ⧸ (levelMap T f (p ^ N)).range) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := hsurj z
      have h0 : evaluation G T p N (x - map T p f y) = 0 := by
        rw [map_sub, evaluation_map, hz, sub_self]
      obtain ⟨w, hw⟩ := exists_smul_eq_of_evaluation_eq_zero G T p _ N h0
      obtain ⟨v, hv⟩ := hdiv w
      refine ⟨y + v, ?_⟩
      rw [map_add, hv, hw, add_sub_cancel]
    · rintro ⟨y, rfl⟩
      exact ⟨evaluation G T p N y, (evaluation_map T p f N y).symm⟩
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π hπsurj).toEquiv, hker]
  rfl

/-- If every section in the kernel of `f` is killed by a positive integer `c`, then the
prime-adic Tate map of `f` is injective. -/
theorem map_injective_of_ker_pow (f : G ⟶ G) (c : ℕ) (hc0 : 0 < c)
    (hc : ∀ s : T ⟶ G.X, s ≫ f.hom.hom = 1 → s ^ c = 1) :
    Function.Injective (map T p f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  obtain ⟨m, hm⟩ : ∃ m, evaluation G T p m x ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    apply Subtype.ext
    funext m
    exact h m
  let s : T ⟶ G.X := (Additive.toMul (evaluation G T p (m + c) x)).val
  have hsf : s ≫ f.hom.hom = 1 := by
    have h := congrArg (fun z => (Additive.toMul (evaluation G T p (m + c) z)).val) hx
    change s ≫ f.hom.hom = (Additive.toMul (evaluation G T p (m + c) 0)).val at h
    rw [map_zero] at h
    exact h
  have hs1 : s ^ c = 1 := hc s hsf
  have hs2 : s ^ (p ^ (m + c)) = 1 :=
    (mem_levelGroup G T _ s).mp (Additive.toMul (evaluation G T p (m + c) x)).property
  have hg : s ^ (Nat.gcd c (p ^ (m + c))) = 1 := pow_gcd_eq_one.mpr ⟨hs1, hs2⟩
  obtain ⟨e, -, hgcd⟩ := (Nat.dvd_prime_pow Fact.out).mp (Nat.gcd_dvd_right c (p ^ (m + c)))
  have hec : e < c := by
    have h1 : p ^ e ≤ c := hgcd ▸ Nat.le_of_dvd hc0 (Nat.gcd_dvd_left _ _)
    have h2 : e < p ^ e := Nat.lt_pow_self (Nat.Prime.one_lt Fact.out)
    omega
  have hpc : s ^ (p ^ c) = 1 := by
    obtain ⟨d, hd⟩ := pow_dvd_pow p hec.le
    rw [hd, pow_mul, ← hgcd, hg, one_pow]
  apply hm
  apply toSection_injective G T (p ^ m)
  rw [toSection_evaluation_add G T p x m c, map_zero]
  change p ^ c • Additive.ofMul s = 0
  rw [← ofMul_pow, hpc]
  rfl

end Langlands.GroupScheme.Tate.PrimeAdic
