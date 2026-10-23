import Langlands.AbelianScheme.Tate.RestrictedProductStatement
import Langlands.AbelianScheme.Tate.PrimeComparisonProof
import Mathlib.RingTheory.Localization.BaseChange

/-! # Rational restricted-product comparisons for actual Tate modules -/

set_option maxHeartbeats 800000

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeAdic
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
variable (p : ℕ) [Fact p.Prime]

/-- The actual prime-adic Tate module has no `p`-torsion: each coordinate is the
transition of the next one, which is `p` times that next coordinate. -/
theorem eq_zero_of_prime_nsmul_eq_zero {z : Integral G T p} (h : p • z = 0) : z = 0 := by
  apply Subtype.ext
  funext n
  apply toSection_injective G T (p ^ n)
  have hz : transition G T (pow_dvd_pow p (Nat.le_succ n)) (z.val (n + 1)) = z.val n :=
    z.property n
  calc toSection G T (p ^ n) (z.val n)
      = toSection G T (p ^ n)
          (transition G T (pow_dvd_pow p (Nat.le_succ n)) (z.val (n + 1))) := by rw [hz]
    _ = p • toSection G T (p ^ (n + 1)) (z.val (n + 1)) := toSection_transition_succ G T p n _
    _ = toSection G T (p ^ (n + 1)) ((p • z).val (n + 1)) := (map_nsmul _ p _).symm
    _ = 0 := by rw [h]; exact map_zero _
    _ = toSection G T (p ^ n) ((0 : Integral G T p).val n) := (map_zero _).symm

theorem eq_zero_of_prime_pow_nsmul_eq_zero (k : ℕ) {z : Integral G T p}
    (h : p ^ k • z = 0) : z = 0 := by
  induction k generalizing z with
  | zero => simpa using h
  | succ k ih =>
    apply eq_zero_of_prime_nsmul_eq_zero G T p
    apply ih
    rw [smul_smul, ← pow_succ]
    exact h

/-- Nonzero `p`-adic integers act injectively on the actual prime-adic Tate module. -/
theorem eq_zero_of_smul_eq_zero {c : ℤ_[p]} (hc : c ≠ 0) {z : Integral G T p}
    (h : c • z = 0) : z = 0 := by
  obtain ⟨u, k, hck⟩ : ∃ (u : ℤ_[p]ˣ) (k : ℕ), c = (u : ℤ_[p]) * (p : ℤ_[p]) ^ k :=
    ⟨_, _, PadicInt.unitCoeff_spec hc⟩
  rw [hck, mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq, ← Nat.cast_pow,
    Nat.cast_smul_eq_nsmul] at h
  exact eq_zero_of_prime_pow_nsmul_eq_zero G T p k h

/-- The canonical rationalization is a localization at the nonzero `p`-adic integers. -/
theorem isLocalizedModule_toRational :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) (toRational G T p) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[p]) ℚ_[p] (toRational G T p)).mpr
    (TensorProduct.isBaseChange ℤ_[p] (Integral G T p) ℚ_[p])

/-- The actual integral prime-adic Tate module embeds in its rationalization. -/
theorem toRational_injective : Function.Injective (toRational G T p) := by
  have := isLocalizedModule_toRational G T p
  intro x y hxy
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ_[p]) hxy
  rw [← sub_eq_zero]
  apply eq_zero_of_smul_eq_zero G T p (nonZeroDivisors.coe_ne_zero c)
  rw [smul_sub, sub_eq_zero]
  simpa only [Submonoid.smul_def] using hc

/-- Every local rational vector has a prime-power multiple in the actual integral image. -/
theorem exists_prime_pow_nsmul_mem_integralImage (y : Rational G T p) :
    ∃ k : ℕ, p ^ k • y ∈ integralImage G T p := by
  have := isLocalizedModule_toRational G T p
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[p]) (toRational G T p) y
  have hsy : (s : ℤ_[p]) • y = toRational G T p x := by
    simpa only [Submonoid.smul_def] using hs
  obtain ⟨u, k, hsk⟩ : ∃ (u : ℤ_[p]ˣ) (k : ℕ), (s : ℤ_[p]) = (u : ℤ_[p]) * (p : ℤ_[p]) ^ k :=
    ⟨_, _, PadicInt.unitCoeff_spec (nonZeroDivisors.coe_ne_zero s)⟩
  refine ⟨k, ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • x, ?_⟩
  rw [map_smul, ← hsy, hsk, mul_smul, smul_smul, Units.inv_mul, one_smul, ← Nat.cast_pow,
    Nat.cast_smul_eq_nsmul]

/-- A natural number prime to `p` is a `p`-adic unit. -/
theorem isUnit_natCast_of_not_dvd {N : ℕ} (hN : ¬ p ∣ N) : IsUnit (N : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  have h2 : ¬ ‖((N : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast]
    exact hN
  rw [Int.cast_natCast] at h2
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp h2)

/-- Integrality is unaffected by multiplication by a natural number prime to `p`. -/
theorem mem_integralImage_of_nsmul_mem {N : ℕ} (hN : ¬ p ∣ N) {w : Rational G T p}
    (h : N • w ∈ integralImage G T p) : w ∈ integralImage G T p := by
  obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd p hN
  have hw : w = ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • (N • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [hw]
  exact Submodule.smul_mem _ _ h

end Langlands.GroupScheme.Tate.PrimeAdic

namespace Langlands.GroupScheme.Tate.PrimeComparison
universe u
open Langlands.TateTwist.Divisibility (AwayPrime)
attribute [local instance] primeFact
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- Every rational Tate vector has a positive natural multiple in the integral image. -/
theorem exists_nsmul_eq_toRational (P : ℕ → Prop) (v : Rational G T P) :
    ∃ N : ℕ, 0 < N ∧ ∃ x : Integral G T P, N • v = toRational G T P x := by
  induction v using TensorProduct.inductionOn with
  | tmul q x =>
    refine ⟨q.den, q.pos, q.num • x, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℚ]
    change (q.den : ℚ) • (q ⊗ₜ[ℤ] x) = (1 : ℚ) ⊗ₜ[ℤ] (q.num • x)
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, zsmul_eq_mul, mul_one,
      mul_comm, Rat.mul_den_eq_num]
  | add v w hv hw =>
    obtain ⟨N, hN, x, hx⟩ := hv
    obtain ⟨M, hM, y, hy⟩ := hw
    refine ⟨N * M, Nat.mul_pos hN hM, M • x + N • y, ?_⟩
    rw [smul_add, mul_comm N M, mul_smul, hx, mul_comm M N, mul_smul, hy, map_add,
      map_nsmul, map_nsmul]

section Generic

variable (P : ℕ → Prop) {I : Type*} (π : I → Nat.Primes)
  (hP : ∀ (i : I) (n : ℕ), P ((π i : ℕ) ^ n))

/-- At all but finitely many indexed primes, the rational coordinate is integral. -/
private theorem eventually_rationalToPrime_mem (hπ : Function.Injective π)
    (v : Rational G T P) :
    ∀ᶠ i in Filter.cofinite, rationalToPrime G T P (π i : ℕ) (hP i) v ∈
      (PrimeAdic.integralImage G T (π i : ℕ)).toAddSubgroup := by
  obtain ⟨N, hN, x, hx⟩ := exists_nsmul_eq_toRational G T P v
  have hfin : {i | (π i : ℕ) ∣ N}.Finite :=
    ((Set.finite_le_nat N).preimage
      ((Subtype.val_injective.comp hπ).injOn)).subset
      (fun i hi => Nat.le_of_dvd hN hi)
  refine hfin.subset (fun i hi => ?_)
  by_contra hd
  apply hi
  apply PrimeAdic.mem_integralImage_of_nsmul_mem G T (π i : ℕ) hd
  rw [← map_nsmul, hx, rationalToPrime_toRational]
  exact ⟨_, rfl⟩

/-- The canonical rational coordinates, landing in the restricted product. -/
private def restrictedCoordinates (hπ : Function.Injective π) :
    Rational G T P →+ RestrictedProduct (fun i : I => PrimeAdic.Rational G T (π i : ℕ))
      (fun i => (PrimeAdic.integralImage G T (π i : ℕ)).toAddSubgroup) Filter.cofinite where
  toFun v := ⟨fun i => rationalToPrime G T P (π i : ℕ) (hP i) v,
    eventually_rationalToPrime_mem G T P π hP hπ v⟩
  map_zero' := by ext i; exact map_zero (rationalToPrime G T P (π i : ℕ) (hP i))
  map_add' v w := by ext i; exact map_add (rationalToPrime G T P (π i : ℕ) (hP i)) v w

private theorem restrictedCoordinates_injective (hπ : Function.Injective π)
    (hinj : Function.Injective (fun x : Integral G T P => fun i => toPrime G T P (π i : ℕ) (hP i) x)) :
    Function.Injective (restrictedCoordinates G T P π hP hπ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨N, hN, x, hx⟩ := exists_nsmul_eq_toRational G T P v
  have hcoord : ∀ i, toPrime G T P (π i : ℕ) (hP i) x = 0 := by
    intro i
    apply PrimeAdic.toRational_injective G T (π i : ℕ)
    have hvi : rationalToPrime G T P (π i : ℕ) (hP i) v = 0 :=
      congrArg (fun y => y i) hv
    rw [map_zero, ← rationalToPrime_toRational, ← hx, map_nsmul, hvi, smul_zero]
  have hx0 : x = 0 := by
    apply hinj
    funext i
    change toPrime G T P (π i : ℕ) (hP i) x = toPrime G T P (π i : ℕ) (hP i) 0
    rw [hcoord i, map_zero]
  have hNv : (N : ℚ) • v = 0 := by
    rw [Nat.cast_smul_eq_nsmul, hx, hx0, map_zero]
  exact (smul_eq_zero.mp hNv).resolve_left (Nat.cast_ne_zero.mpr hN.ne')

private theorem restrictedCoordinates_surjective (hπ : Function.Injective π)
    (hsurj : Function.Surjective (fun x : Integral G T P => fun i => toPrime G T P (π i : ℕ) (hP i) x)) :
    Function.Surjective (restrictedCoordinates G T P π hP hπ) := by
  classical
  intro y
  have hE : {i | ¬ y i ∈ (PrimeAdic.integralImage G T (π i : ℕ)).toAddSubgroup}.Finite :=
    Filter.eventually_cofinite.mp y.property
  choose k hk using fun i => PrimeAdic.exists_prime_pow_nsmul_mem_integralImage G T (π i : ℕ) (y i)
  let N : ℕ := ∏ i ∈ hE.toFinset, (π i : ℕ) ^ k i
  have hN : 0 < N := Finset.prod_pos (fun i _ => pow_pos (π i).property.pos _)
  have hNy : ∀ i, N • y i ∈ PrimeAdic.integralImage G T (π i : ℕ) := by
    intro i
    by_cases hi : i ∈ hE.toFinset
    · obtain ⟨M, hM⟩ : (π i : ℕ) ^ k i ∣ N := Finset.dvd_prod_of_mem _ hi
      rw [hM, mul_comm, mul_smul]
      exact (PrimeAdic.integralImage G T (π i : ℕ)).toAddSubgroup.nsmul_mem (hk i) M
    · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi
      exact (PrimeAdic.integralImage G T (π i : ℕ)).toAddSubgroup.nsmul_mem hi N
  choose z hz using hNy
  obtain ⟨x, hxz⟩ := hsurj z
  refine ⟨(N : ℚ)⁻¹ • toRational G T P x, ?_⟩
  ext i
  change rationalToPrime G T P (π i : ℕ) (hP i) ((N : ℚ)⁻¹ • toRational G T P x) = y i
  have hxi : toPrime G T P (π i : ℕ) (hP i) x = z i := congrArg (fun f => f i) hxz
  rw [map_smul, rationalToPrime_toRational, hxi, hz i, ← Nat.cast_smul_eq_nsmul ℚ,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr hN.ne')]

/-- The generic exact-coordinate rational restricted-product comparison. -/
private theorem restrictedComparison (hπ : Function.Injective π)
    (hbij : Function.Bijective (fun x : Integral G T P => fun i => toPrime G T P (π i : ℕ) (hP i) x)) :
    ∃ e : Rational G T P ≃+ RestrictedProduct (fun i : I => PrimeAdic.Rational G T (π i : ℕ))
      (fun i => (PrimeAdic.integralImage G T (π i : ℕ)).toAddSubgroup) Filter.cofinite,
      ∀ (v : Rational G T P) (i : I), e v i = rationalToPrime G T P (π i : ℕ) (hP i) v :=
  ⟨AddEquiv.ofBijective (restrictedCoordinates G T P π hP hπ)
    ⟨restrictedCoordinates_injective G T P π hP hπ hbij.1,
      restrictedCoordinates_surjective G T P π hP hπ hbij.2⟩, fun _ _ => rfl⟩

end Generic

/-- The full rational Tate module is the actual rational restricted product. -/
theorem rationalRestrictedProductComparison : RationalRestrictedProductComparison G T := by
  obtain ⟨e, he, -, -⟩ := fullPrimeProductComparison G T
  have hbij : Function.Bijective (toPrimeProduct G T) := by
    rw [← he]
    exact e.bijective
  exact restrictedComparison G T (fun _ => True) (fun p => p) (fun _ _ => trivial)
    Function.injective_id hbij

/-- Every away rational Tate module is the actual rational restricted product over
the retained primes. -/
theorem rationalAwayRestrictedProductComparison (m : ℕ) :
    RationalAwayRestrictedProductComparison G T m := by
  obtain ⟨e, he, -, -⟩ := awayPrimeProductComparison G T m
  have hbij : Function.Bijective (toAwayPrimeProduct G T m) := by
    rw [← he]
    exact e.bijective
  exact restrictedComparison G T (fun n => Nat.Coprime n m) (fun p : AwayPrime m => p.val)
    (fun p n => p.property.pow_left n) Subtype.val_injective hbij

/-- Full and all away rational restricted-product comparisons. -/
theorem rationalRestrictedProductComparisons : RationalRestrictedProductComparisons G T :=
  ⟨rationalRestrictedProductComparison G T, rationalAwayRestrictedProductComparison G T⟩

end Langlands.GroupScheme.Tate.PrimeComparison
