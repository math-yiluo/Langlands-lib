import Langlands.AbelianScheme.Tate.PrimeAdic
import Langlands.AbelianScheme.Tate.Twist
import Mathlib.RingTheory.Localization.BaseChange

/-! # Torsion-freeness of prime-adic Tate modules and rational separation -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.PrimeAdicSeparation

universe u

variable {p : ℕ} [Fact p.Prime]

/-- In a `ℤ_[p]`-module without `p`-torsion, every nonzero p-adic integer is a
non-zero-divisor. -/
theorem eq_zero_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (hM : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0) {c : ℤ_[p]} (hc : c ≠ 0) {x : M}
    (h : c • x = 0) : x = 0 := by
  have hpow : ∀ (k : ℕ) (y : M), (p : ℤ_[p]) ^ k • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, mul_smul] at hy
      exact hM y (ih _ hy)
  rw [PadicInt.unitCoeff_spec hc, mul_smul] at h
  apply hpow c.valuation x
  have h' : ((↑(PadicInt.unitCoeff hc)⁻¹ : ℤ_[p]) * ↑(PadicInt.unitCoeff hc)) •
      ((p : ℤ_[p]) ^ c.valuation • x) = 0 := by
    rw [mul_smul, h, smul_zero]
  rwa [Units.inv_mul, one_smul] at h'

private lemma isLocalizedModule_tensor (M : Type*) [AddCommGroup M] [Module ℤ_[p] M] :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) (TensorProduct.mk ℤ_[p] ℚ_[p] M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[p]) ℚ_[p] _).mpr
    (TensorProduct.isBaseChange ℤ_[p] M ℚ_[p])

/-- Over a module without `p`-torsion, `1 ⊗ w` vanishes only for `w = 0`. -/
theorem eq_zero_of_one_tmul_eq_zero {W : Type*} [AddCommGroup W] [Module ℤ_[p] W]
    (hW : ∀ w : W, (p : ℤ_[p]) • w = 0 → w = 0) {w : W}
    (h : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] w = 0) : w = 0 := by
  have := isLocalizedModule_tensor (p := p) W
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] W 1)).mp h
  exact eq_zero_of_smul_eq_zero hW (nonZeroDivisors.coe_ne_zero c) hc

/-- Every rational element has a nonzero p-adic integral multiple of the form `1 ⊗ x`. -/
theorem exists_smul_eq_one_tmul {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (X : ℚ_[p] ⊗[ℤ_[p]] M) :
    ∃ c : ℤ_[p], c ≠ 0 ∧ ∃ x : M, c • X = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x := by
  have := isLocalizedModule_tensor (p := p) M
  obtain ⟨⟨x, c⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] M 1) X
  refine ⟨c, nonZeroDivisors.coe_ne_zero c, x, ?_⟩
  exact IsLocalizedModule.mk'_cancel' (TensorProduct.mk ℤ_[p] ℚ_[p] M 1) x c

/-- A rational element with zero integral multiple is zero. -/
theorem eq_zero_of_smul_eq_zero_rational {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    {c : ℤ_[p]} (hc : c ≠ 0) {X : ℚ_[p] ⊗[ℤ_[p]] M} (h : c • X = 0) : X = 0 := by
  have h' : ((c : ℚ_[p])) • X = 0 := by
    rw [← h]
    exact (algebraMap_smul ℚ_[p] c X)
  have hc' : (c : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.2 hc
  exact (smul_eq_zero.mp h').resolve_left hc'

variable {M N W : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup N] [Module ℤ_[p] N]
  [AddCommGroup W] [Module ℤ_[p] W]

/-- A rationalized pairing is left-separating when its integral values have no
`p`-torsion and the integral pairing is left-separating. -/
theorem separatingLeft_of_tmul (hW : ∀ w : W, (p : ℤ_[p]) • w = 0 → w = 0)
    (b : M → N → W)
    (B : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] N →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] W)
    (hB : ∀ (q r : ℚ_[p]) x y, B (q ⊗ₜ[ℤ_[p]] x) (r ⊗ₜ[ℤ_[p]] y) = (q * r) ⊗ₜ[ℤ_[p]] b x y)
    (hb : ∀ x, (∀ y, b x y = 0) → x = 0) : B.SeparatingLeft := by
  intro X hX
  obtain ⟨c, hc, x, hcx⟩ := exists_smul_eq_one_tmul X
  have hxy : ∀ y, b x y = 0 := by
    intro y
    apply eq_zero_of_one_tmul_eq_zero hW
    have h1 := hB 1 1 x y
    rw [one_mul, ← hcx, LinearMap.map_smul_of_tower, LinearMap.smul_apply, hX, smul_zero] at h1
    exact h1.symm
  rw [hb x hxy, TensorProduct.tmul_zero] at hcx
  exact eq_zero_of_smul_eq_zero_rational hc hcx

/-- A rationalized pairing is right-separating when its integral values have no
`p`-torsion and the integral pairing is right-separating. -/
theorem separatingRight_of_tmul (hW : ∀ w : W, (p : ℤ_[p]) • w = 0 → w = 0)
    (b : M → N → W)
    (B : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] N →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] W)
    (hB : ∀ (q r : ℚ_[p]) x y, B (q ⊗ₜ[ℤ_[p]] x) (r ⊗ₜ[ℤ_[p]] y) = (q * r) ⊗ₜ[ℤ_[p]] b x y)
    (hb : ∀ y, (∀ x, b x y = 0) → y = 0) : B.SeparatingRight := by
  intro Y hY
  obtain ⟨c, hc, y, hcy⟩ := exists_smul_eq_one_tmul Y
  have hxy : ∀ x, b x y = 0 := by
    intro x
    apply eq_zero_of_one_tmul_eq_zero hW
    have h1 := hB 1 1 x y
    rw [one_mul, ← hcy, LinearMap.map_smul_of_tower, hY, smul_zero] at h1
    exact h1.symm
  rw [hb y hxy, TensorProduct.tmul_zero] at hcy
  exact eq_zero_of_smul_eq_zero_rational hc hcy

end Langlands.PrimeAdicSeparation

namespace Langlands.GroupScheme.Tate.PrimeAdic

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
  (p : ℕ) [Fact p.Prime]

lemma evaluation_natCast_smul (n k : ℕ) (x : Integral G T p) :
    evaluation G T p n ((k : ℤ_[p]) • x) = k • evaluation G T p n x := by
  rw [evaluation_smul, map_natCast]
  exact Nat.cast_smul_eq_nsmul (ZMod (p ^ n)) k _

/-- The actual prime-adic Tate module has no `p`-torsion. -/
theorem eq_zero_of_prime_smul_eq_zero (x : Integral G T p)
    (h : (p : ℤ_[p]) • x = 0) : x = 0 := by
  apply Subtype.ext
  funext n
  have hn := congrArg (evaluation G T p (n + 1)) h
  rw [evaluation_natCast_smul, map_zero] at hn
  apply toSection_injective G T (p ^ n)
  change toSection G T (p ^ n) (evaluation G T p n x) = toSection G T (p ^ n) 0
  rw [← evaluation_transition G T p n x, toSection_transition_succ, ← map_nsmul, hn,
    map_zero, map_zero]

/-- If all successive transitions are surjective, so is every coordinate projection. -/
theorem evaluation_surjective
    (hsurj : ∀ (n : ℕ) (y : Level G T (p ^ n)),
      ∃ x : Level G T (p ^ (n + 1)), transition G T (pow_dvd_pow p (Nat.le_succ n)) x = y)
    (n : ℕ) : Function.Surjective (evaluation G T p n) := by
  intro y
  let w : (k : ℕ) → Level G T (p ^ (n + k)) := fun k =>
    Nat.rec (motive := fun k => Level G T (p ^ (n + k))) y
      (fun k z => Classical.choose (hsurj (n + k) z)) k
  have hw : ∀ k, transition G T (pow_dvd_pow p (Nat.le_succ (n + k))) (w (k + 1)) = w k :=
    fun k => Classical.choose_spec (hsurj (n + k) (w k))
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hw0 : ∀ k, transition G T (pow_dvd_pow p (Nat.le_add_right n k)) (w k) = y := by
    intro k
    induction k with
    | zero => exact transition_self G T hpos y
    | succ k ih =>
      rw [← hw k, transition_comp] at ih
      exact ih
  let x : Integral G T p := ⟨fun m => transition G T (pow_dvd_pow p (Nat.le_add_left m n)) (w m),
    by
      intro m
      change transition G T _ (transition G T _ (w (m + 1))) =
        transition G T _ (w m)
      rw [← hw m, transition_comp, transition_comp]
      rfl⟩
  exact ⟨x, hw0 n⟩

/-- If every point has a `p`-th root, every successive transition is surjective. -/
theorem transition_succ_surjective_of_pow (hdiv : ∀ y : T ⟶ G.X, ∃ x, x ^ p = y)
    (n : ℕ) (y : Level G T (p ^ n)) :
    ∃ x : Level G T (p ^ (n + 1)), transition G T (pow_dvd_pow p (Nat.le_succ n)) x = y := by
  obtain ⟨x, hx⟩ := hdiv (Additive.toMul y).val
  have hmem : x ∈ levelGroup G T (p ^ (n + 1)) := by
    rw [mem_levelGroup, pow_succ', pow_mul, hx]
    exact (mem_levelGroup G T (p ^ n) _).mp (Additive.toMul y).property
  refine ⟨Additive.ofMul ⟨x, hmem⟩, ?_⟩
  apply toSection_injective G T (p ^ n)
  rw [toSection_transition_succ]
  change Additive.ofMul (x ^ p) = Additive.ofMul (Additive.toMul y).val
  rw [hx]

/-- If every point has a `p`-th root, every coordinate projection is surjective. -/
theorem evaluation_surjective_of_pow (hdiv : ∀ y : T ⟶ G.X, ∃ x, x ^ p = y) (n : ℕ) :
    Function.Surjective (evaluation G T p n) :=
  evaluation_surjective G T p (transition_succ_surjective_of_pow G T p hdiv) n

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- A quasi-inverse on points, with composite the `N`-th power, makes the image of
the induced Tate map contain `N` times every element. -/
theorem exists_map_eq_natCast_smul (f : G ⟶ H) (N : ℕ)
    (ψ : (T ⟶ H.X) →* (T ⟶ G.X)) (hψ : ∀ y, ψ y ≫ f.hom.hom = y ^ N)
    (z : Integral H T p) : ∃ y : Integral G T p, map T p f y = (N : ℤ_[p]) • z := by
  have hmem : ∀ (m : ℕ) (w : Level H T m), ψ (Additive.toMul w).val ∈ levelGroup G T m := by
    intro m w
    rw [mem_levelGroup, ← map_pow, (mem_levelGroup H T m _).mp (Additive.toMul w).property,
      map_one]
  let c : (n : ℕ) → Level G T (p ^ n) := fun n =>
    Additive.ofMul ⟨ψ (Additive.toMul (z.val n)).val, hmem _ _⟩
  have hc : ∀ n, transition G T (pow_dvd_pow p (Nat.le_succ n)) (c (n + 1)) = c n := by
    intro n
    have hz := congrArg (fun w : Level H T (p ^ n) => (Additive.toMul w).val) (z.property n)
    apply toSection_injective G T (p ^ n)
    change Additive.ofMul ((ψ (Additive.toMul (z.val (n + 1))).val) ^ (p ^ (n + 1) / p ^ n)) =
      Additive.ofMul (ψ (Additive.toMul (z.val n)).val)
    rw [← map_pow]
    exact congrArg (fun w => Additive.ofMul (ψ w)) hz
  refine ⟨⟨c, hc⟩, ?_⟩
  apply Subtype.ext
  funext n
  change levelMap T f (p ^ n) (c n) = evaluation H T p n ((N : ℤ_[p]) • z)
  rw [evaluation_natCast_smul]
  apply toSection_injective H T (p ^ n)
  rw [map_nsmul]
  change Additive.ofMul (ψ (Additive.toMul (z.val n)).val ≫ f.hom.hom) =
    Additive.ofMul ((Additive.toMul (z.val n)).val ^ N)
  rw [hψ]

/-- If the kernel points of `f` are killed by a positive `N`, the induced map on
the prime-adic Tate module is injective. -/
theorem eq_zero_of_map_eq_zero (f : G ⟶ H) {N : ℕ} (hN : 0 < N)
    (hker : ∀ x : T ⟶ G.X, x ≫ f.hom.hom = 1 → x ^ N = 1)
    (y : Integral G T p) (hy : map T p f y = 0) : y = 0 := by
  apply PrimeAdicSeparation.eq_zero_of_smul_eq_zero (eq_zero_of_prime_smul_eq_zero G T p)
    (Nat.cast_ne_zero.mpr hN.ne' : (N : ℤ_[p]) ≠ 0)
  apply Subtype.ext
  funext n
  change evaluation G T p n ((N : ℤ_[p]) • y) = 0
  rw [evaluation_natCast_smul]
  apply toSection_injective G T (p ^ n)
  rw [map_nsmul, map_zero]
  have h := congrArg (fun w : Level H T (p ^ n) => (Additive.toMul w).val)
    (congrArg (evaluation H T p n) hy)
  exact congrArg Additive.ofMul (hker _ h)

end Langlands.GroupScheme.Tate.PrimeAdic

namespace Langlands.TateTwist

universe u

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]

lemma evaluation_natCast_smul (n k : ℕ) (x : Integral R p) :
    evaluation R p n ((k : ℤ_[p]) • x) = k • evaluation R p n x := by
  rw [evaluation_smul, map_natCast]
  exact Nat.cast_smul_eq_nsmul (ZMod (p ^ n)) k _

/-- The actual integral roots-of-unity twist has no `p`-torsion. -/
theorem eq_zero_of_prime_smul_eq_zero (x : Integral R p)
    (h : (p : ℤ_[p]) • x = 0) : x = 0 := by
  apply Subtype.ext
  funext n
  have hn := congrArg (evaluation R p (n + 1)) h
  rw [evaluation_natCast_smul, map_zero] at hn
  apply toUnit_injective R (p ^ n)
  change toUnit R (p ^ n) (evaluation R p n x) = toUnit R (p ^ n) 0
  rw [← evaluation_transition R p n x, toUnit_transition_succ, ← map_nsmul, hn,
    map_zero, map_zero]

end Langlands.TateTwist
