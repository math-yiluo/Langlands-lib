import Langlands.Shimura.Unitary.Adelic
import Langlands.Shimura.Unitary.Positivity
import Langlands.Global.AdeleQuotientCompactProof

/-!
# Finiteness of rational points in compact levels of a definite similitude group

For an involution `σ` of a finite-dimensional `ℚ`-algebra `A` whose real scalar extension is
positive, the rational similitudes lying in a compact subgroup of the finite adelic points form a
finite set. Consequently every rational similitude lying in a conjugate of a compact level has
finite order.

* `Langlands.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact`: a compact set of finite
  adeles has bounded denominators; `exists_intCast_mul_eq_of_isCompact` is the rational case.
* `Langlands.Global.rat_eq_one_or_eq_neg_one_of_forall_zpow`: a rational number all of whose
  powers have bounded denominators is `±1`.
* `AlgebraInvolution.exists_abs_repr_le_of_isPositive`: positivity bounds the coordinates of
  the elements `x` with `σ(x) x = c ≤ 1`.
* `AlgebraInvolution.finite_comap_finiteAdelicDiagonal`: the rational similitudes in a compact
  subgroup of the finite adelic points form a finite set.
* `AlgebraInvolution.arithmeticSubgroup`: the arithmetic subgroup `GJ(ℚ) ∩ g K g⁻¹`;
  `finite_arithmeticSubgroup`: it is finite for compact `K`.
* `AlgebraInvolution.isOfFinOrder_of_conj_mem`: rational similitudes in a conjugate of a compact
  subgroup have finite order.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

universe v

namespace Langlands.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

section Denominators

variable {K : Type*} [Field K] [NumberField K]

/-- Global integers are integral at every finite place. -/
theorem algebraMap_integer_mem_integralFiniteAdeles (d : 𝓞 K) :
    algebraMap (𝓞 K) (FiniteAdeles K) d ∈ integralFiniteAdeles K := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (FiniteAdeles K)]
  exact (mem_integralFiniteAdeles K _).2 fun v => coe_mem_adicCompletionIntegers v d

/-- Every finite adele becomes integral after multiplication by a nonzero global integer. -/
theorem exists_mul_mem_integralFiniteAdeles (a : FiniteAdeles K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ algebraMap (𝓞 K) (FiniteAdeles K) d * a ∈ integralFiniteAdeles K := by
  obtain ⟨d, hd0, hd⟩ := exists_integer_mul_mem_adicCompletionIntegers a
  exact ⟨d, hd0, (mem_integralFiniteAdeles K _).2 fun v => hd v⟩

/-- A compact set of finite adeles has bounded denominators: one nonzero global integer
multiplies all of it into `∏_v 𝒪_v`. -/
theorem exists_mul_mem_integralFiniteAdeles_of_isCompact {C : Set (FiniteAdeles K)}
    (hC : IsCompact C) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ a ∈ C,
      algebraMap (𝓞 K) (FiniteAdeles K) d * a ∈ integralFiniteAdeles K := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun b : FiniteAdeles K =>
      (fun x => x - b) ⁻¹' (integralFiniteAdeles K : Set (FiniteAdeles K)))
    (fun b => (isOpen_integralFiniteAdeles K).preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by
      show x - x ∈ integralFiniteAdeles K
      rw [sub_self]
      exact (integralFiniteAdeles K).zero_mem⟩)
  choose d hd0 hd using fun b : FiniteAdeles K => exists_mul_mem_integralFiniteAdeles b
  refine ⟨∏ b ∈ t, d b, Finset.prod_ne_zero_iff.2 fun b _ => hd0 b, fun x hx => ?_⟩
  obtain ⟨b, hbt, hxb⟩ := Set.mem_iUnion₂.1 (ht hx)
  change x - b ∈ integralFiniteAdeles K at hxb
  rw [← sub_add_cancel x b, mul_add]
  refine add_mem (mul_mem (algebraMap_integer_mem_integralFiniteAdeles _) hxb) ?_
  rw [← Finset.mul_prod_erase t d hbt, map_mul, mul_comm (algebraMap _ _ (d b)), mul_assoc]
  exact mul_mem (algebraMap_integer_mem_integralFiniteAdeles _) (hd b)

/-- A rational number that is integral at every finite place is an integer. -/
theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeles ℚ) q ∈ integralFiniteAdeles ℚ) : ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q fun v => by
    have h := (mem_integralFiniteAdeles ℚ _).1 hq v
    rw [mem_adicCompletionIntegers] at h
    rwa [FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation'] at h
  exact ⟨Rat.ringOfIntegersEquiv y, by rw [Rat.ringOfIntegersEquiv_apply_coe, hy]⟩

/-- Rational points of a compact set of finite adeles have bounded denominators. -/
theorem exists_intCast_mul_eq_of_isCompact {C : Set (FiniteAdeles ℚ)} (hC : IsCompact C) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ q : ℚ, algebraMap ℚ (FiniteAdeles ℚ) q ∈ C →
      ∃ z : ℤ, (z : ℚ) = N * q := by
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hC
  refine ⟨Rat.ringOfIntegersEquiv d, (map_ne_zero_iff _ Rat.ringOfIntegersEquiv.injective).2 hd0,
    fun q hq => ?_⟩
  have h := hd _ hq
  rw [IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ (FiniteAdeles ℚ), ← map_mul] at h
  rw [Rat.ringOfIntegersEquiv_apply_coe]
  exact exists_intCast_eq_of_mem_integralFiniteAdeles h

/-- If `N q` is an integer for a nonzero integer `N`, the denominator of `q` divides `|N|`. -/
theorem rat_den_dvd_natAbs_of_intCast_eq_mul {N z : ℤ} {q : ℚ} (hN : N ≠ 0)
    (h : (z : ℚ) = N * q) : q.den ∣ N.natAbs := by
  have hq : q = (z : ℚ) / N := by
    rw [h, mul_div_cancel_left₀ _ (Int.cast_ne_zero.2 hN)]
  have := Rat.den_dvd z N
  rw [Rat.divInt_eq_div, ← hq] at this
  exact Int.natCast_dvd.1 this

/-- A nonzero rational number all of whose integral powers have denominators dividing a fixed
nonzero integer is `1` or `-1`. -/
theorem rat_eq_one_or_eq_neg_one_of_forall_zpow {N : ℤ} (hN : N ≠ 0) {c : ℚ} (hc : c ≠ 0)
    (h : ∀ k : ℤ, ∃ z : ℤ, (z : ℚ) = N * c ^ k) : c = 1 ∨ c = -1 := by
  have key : ∀ q : ℚ, (∀ k : ℕ, ∃ z : ℤ, (z : ℚ) = N * q ^ k) → q.den = 1 := by
    intro q hq
    by_contra hne
    have h2 : 1 < q.den := by have := q.den_pos; omega
    obtain ⟨z, hz⟩ := hq N.natAbs
    have hd := rat_den_dvd_natAbs_of_intCast_eq_mul hN hz
    rw [Rat.den_pow] at hd
    have hle := Nat.le_of_dvd (Int.natAbs_pos.2 hN) hd
    have hlt : N.natAbs < q.den ^ N.natAbs := Nat.lt_pow_self h2
    omega
  have h1 := key c fun k => by simpa using h k
  have h2 := key c⁻¹ fun k => by
    obtain ⟨z, hz⟩ := h (-(k : ℤ))
    exact ⟨z, by rw [hz, zpow_neg, zpow_natCast, inv_pow]⟩
  rw [Rat.den_inv_of_ne_zero hc] at h2
  have hc' : (c.num : ℚ) = c := (Rat.den_eq_one_iff c).1 h1
  rcases Int.natAbs_eq_iff.1 h2 with h3 | h3
  · left
    rw [← hc', h3]
    norm_num
  · right
    rw [← hc', h3]
    norm_num

/-- Rational numbers with denominators dividing `N` and absolute value at most `M` form a
finite set. -/
theorem finite_setOf_rat_intCast_eq_mul_abs_le (N : ℤ) (hN : N ≠ 0) (M : ℚ) :
    {q : ℚ | (∃ z : ℤ, (z : ℚ) = N * q) ∧ |q| ≤ M}.Finite := by
  refine ((Set.finite_Icc (-⌈|(N : ℚ)| * M⌉) ⌈|(N : ℚ)| * M⌉).image
    fun z : ℤ => (z : ℚ) / N).subset ?_
  rintro q ⟨⟨z, hz⟩, hq⟩
  refine ⟨z, ?_, show (z : ℚ) / N = q by rw [hz, mul_div_cancel_left₀ _ (Int.cast_ne_zero.2 hN)]⟩
  have hzq : |(z : ℚ)| ≤ |(N : ℚ)| * M := by
    rw [hz, abs_mul]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have h1 : |z| ≤ ⌈|(N : ℚ)| * M⌉ := by
    have : ((|z| : ℤ) : ℚ) ≤ |(N : ℚ)| * M := by rw [Int.cast_abs]; exact hzq
    exact Int.cast_le.1 (this.trans (Int.le_ceil _))
  exact ⟨by linarith [neg_abs_le z], (le_abs_self z).trans h1⟩

end Denominators

end Langlands.Global

namespace Langlands.Shimura.AlgebraInvolution

open Module Langlands.Global

variable {A : Type v} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]

/-- For an involution whose real scalar extension is positive, the coordinates of the elements
`x` with `σ(x) x = c ≤ 1` (`c` rational) are bounded in any basis. The bound comes from the
positive definite quadratic form `y ↦ tr_ℝ(σ(y) y)` on `ℝ ⊗ A`. -/
theorem exists_abs_repr_le_of_isPositive (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) {ι : Type*} [Fintype ι] (b : Basis ι ℚ A) :
    ∃ M : ℚ, ∀ (x : A) (c : ℚ), σ x * x = algebraMap ℚ A c → c ≤ 1 →
      ∀ i, |b.repr x i| ≤ M := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun x c _ _ i => isEmptyElim i⟩
  let bR := Algebra.TensorProduct.basis ℝ b
  let τ := σ.baseChange ℝ
  let tf : ℝ ⊗[ℚ] A →ₗ[ℝ] ℝ :=
    (LinearMap.trace ℝ (ℝ ⊗[ℚ] A)) ∘ₗ LinearMap.mul ℝ (ℝ ⊗[ℚ] A)
  let Q : (ι → ℝ) → ℝ := fun v => tf (τ (bR.equivFun.symm v) * bR.equivFun.symm v)
  have hQ : ∀ v, Q v = ∑ i, ∑ j, v i * v j * tf (τ (bR i) * bR j) := by
    intro v
    have hv : Q v = tf (τ.linear (∑ i, v i • bR i) * ∑ j, v j • bR j) := by
      simp only [Q, Basis.equivFun_symm_apply]
    rw [hv, map_sum, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_mul_smul_comm, map_smul, smul_eq_mul]
  have hQcont : Continuous Q := by
    have : Q = fun v => ∑ i, ∑ j, v i * v j * tf (τ (bR i) * bR j) := funext hQ
    rw [this]
    fun_prop
  have hQsmul : ∀ (t : ℝ) v, Q (t • v) = t ^ 2 * Q v := by
    intro t v
    rw [hQ, hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hQpos : ∀ v, v ≠ 0 → 0 < Q v := fun v hv =>
    hpos _ (bR.equivFun.symm.map_ne_zero_iff.2 hv)
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hQcont.continuousOn
  have hv₀0 : v₀ ≠ 0 := by
    rintro rfl
    simp at hv₀
  set m := Q v₀
  have hm : 0 < m := hQpos v₀ hv₀0
  have hlow : ∀ v, m * ‖v‖ ^ 2 ≤ Q v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simpa using (hQsmul 0 0).ge
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have h1 := hmin hu
    have h2 : Q v = ‖v‖ ^ 2 * Q (‖v‖⁻¹ • v) := by
      rw [← hQsmul, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [h2, mul_comm m]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  set d : ℝ := (finrank ℝ (ℝ ⊗[ℚ] A) : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  refine ⟨⌈1 + d / m⌉₊, fun x c hx hc i => ?_⟩
  set v := bR.equivFun (1 ⊗ₜ x)
  have hvi : ∀ j, v j = (b.repr x j : ℝ) := fun j => by
    simp [v, bR, Algebra.TensorProduct.basis_repr_tmul]
  have hQv : Q v = c * d := by
    change tf (τ (bR.equivFun.symm v) * bR.equivFun.symm v) = _
    rw [LinearEquiv.symm_apply_apply]
    change tf ((1 : ℝ) ⊗ₜ[ℚ] σ x * (1 ⊗ₜ x)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hx, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, ← algebraMap_smul ℝ c, map_smul, ← Algebra.TensorProduct.one_def]
    change (c : ℝ) • LinearMap.trace ℝ _ (LinearMap.mulLeft ℝ 1) = _
    rw [LinearMap.mulLeft_one, LinearMap.trace_id, smul_eq_mul]
  have hle : m * ‖v‖ ^ 2 ≤ d := by
    calc m * ‖v‖ ^ 2 ≤ Q v := hlow v
      _ = c * d := hQv
      _ ≤ 1 * d := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hd
      _ = d := one_mul d
  have hvi_le : |v i| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v i
  have hsq : |v i| ^ 2 ≤ d / m := by
    rw [le_div_iff₀ hm]
    calc |v i| ^ 2 * m ≤ ‖v‖ ^ 2 * m :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hvi_le 2) hm.le
      _ ≤ d := by rw [mul_comm]; exact hle
  have habs : |v i| ≤ 1 + d / m := by nlinarith [abs_nonneg (v i)]
  have : ((|b.repr x i| : ℚ) : ℝ) ≤ ((⌈1 + d / m⌉₊ : ℚ) : ℝ) := by
    rw [Rat.cast_abs, ← hvi, Rat.cast_natCast]
    exact habs.trans (Nat.le_ceil _)
  exact_mod_cast this


/-- For an involution whose real scalar extension is positive, the rational similitudes whose
diagonal image lies in a compact subgroup of the finite adelic points form a finite set. -/
theorem finite_comap_finiteAdelicDiagonal (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) {H : Subgroup σ.FiniteAdelicPoints}
    (hH : IsCompact (H : Set σ.FiniteAdelicPoints)) :
    (H.comap σ.finiteAdelicDiagonal : Set σ.similitudes).Finite := by
  classical
  let b := Module.finBasis ℚ A
  obtain ⟨M, hM⟩ := exists_abs_repr_le_of_isPositive σ hpos b
  -- The multipliers of `H` form a compact set of finite adeles.
  have hcm : Continuous fun g : σ.FiniteAdelicPoints =>
      ((Points.multiplier σ (FiniteAdeles ℚ) g : (FiniteAdeles ℚ)ˣ) : FiniteAdeles ℚ) :=
    Units.continuous_val.comp (Points.continuous_multiplier σ _)
  obtain ⟨N, hN0, hN⟩ := exists_intCast_mul_eq_of_isCompact (hH.image hcm)
  -- So do the coordinates of the elements of `H` in the basis `b`.
  let : TopologicalSpace (FiniteAdeles ℚ ⊗[ℚ] A) :=
    moduleTopology (FiniteAdeles ℚ) (FiniteAdeles ℚ ⊗[ℚ] A)
  let e := coordinateEquiv (FiniteAdeles ℚ) b
  have hcoord : ∀ i, Continuous fun g : σ.FiniteAdelicPoints =>
      e ((g.1.1 : (FiniteAdeles ℚ ⊗[ℚ] A)ˣ) : FiniteAdeles ℚ ⊗[ℚ] A) i := fun i =>
    (continuous_apply i).comp (e.continuous.comp
      (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)))
  choose Nc hNc0 hNc using fun i => exists_intCast_mul_eq_of_isCompact (hH.image (hcoord i))
  let S : Fin (finrank ℚ A) → Set ℚ := fun i =>
    {q : ℚ | (∃ z : ℤ, (z : ℚ) = Nc i * q) ∧ |q| ≤ M}
  have hS : (Set.pi Set.univ S ×ˢ ({1, -1} : Set ℚ)).Finite :=
    (Set.Finite.pi fun i => finite_setOf_rat_intCast_eq_mul_abs_le _ (hNc0 i) M).prod
      (Set.toFinite _)
  let F : σ.similitudes → (Fin (finrank ℚ A) → ℚ) × ℚ :=
    fun γ => (b.equivFun (γ.1.1 : A), (γ.1.2 : ℚ))
  have hF : Function.Injective F := fun γ δ h =>
    Subtype.ext (Prod.ext (Units.ext (b.equivFun.injective (congrArg Prod.fst h)))
      (Units.ext (congrArg Prod.snd h)))
  refine (hS.preimage hF.injOn).subset fun γ hγ => ?_
  change σ.finiteAdelicDiagonal γ ∈ H at hγ
  set x : A := (γ.1.1 : A)
  set c : ℚ := (γ.1.2 : ℚ)
  -- The multiplier is `±1`: all its powers are multipliers of elements of `H`.
  have hcpm : c = 1 ∨ c = -1 := by
    refine rat_eq_one_or_eq_neg_one_of_forall_zpow hN0 (Units.ne_zero _) fun k => hN _ ?_
    refine ⟨σ.finiteAdelicDiagonal (γ ^ k), ?_, ?_⟩
    · rw [map_zpow]
      exact H.zpow_mem hγ k
    · change algebraMap ℚ (FiniteAdeles ℚ) ((σ.multiplier (γ ^ k) : ℚˣ) : ℚ) = _
      rw [map_zpow σ.multiplier, Units.val_zpow_eq_zpow_val]
      rfl
  have hc1 : c ≤ 1 := by
    rcases hcpm with h | h <;> norm_num [h]
  have hx : σ x * x = algebraMap ℚ A c := by
    have h1 : x * σ x = algebraMap ℚ A c := (σ.mem_similitudes_iff γ.1).1 γ.2
    have h2 : σ x = ((γ.1.1⁻¹ : Aˣ) : A) * algebraMap ℚ A c := by
      rw [← h1, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2, mul_assoc, Algebra.commutes c x, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨fun i _ => ⟨hNc i (b.repr x i) ⟨σ.finiteAdelicDiagonal γ, hγ, ?_⟩, hM x c hx hc1 i⟩, ?_⟩
  · change Algebra.TensorProduct.equivPiOfFiniteBasis (FiniteAdeles ℚ) b
      ((1 : FiniteAdeles ℚ) ⊗ₜ x) i = _
    simp [Algebra.TensorProduct.equivPiOfFiniteBasis_apply, Algebra.algebraMap_eq_smul_one]
  · change c ∈ ({1, -1} : Set ℚ)
    rcases hcpm with h | h
    · exact Or.inl h
    · exact Or.inr h

omit [Module.Finite ℚ A] in
/-- The arithmetic subgroup `GJ(ℚ) ∩ g K g⁻¹`: the rational similitudes whose diagonal image lies
in the conjugate `g K g⁻¹` of a subgroup `K` of the finite adelic points. -/
def arithmeticSubgroup (σ : AlgebraInvolution ℚ A) (K : Subgroup σ.FiniteAdelicPoints)
    (g : σ.FiniteAdelicPoints) : Subgroup σ.similitudes :=
  (K.map (MulAut.conj g).toMonoidHom).comap σ.finiteAdelicDiagonal

omit [Module.Finite ℚ A] in
theorem mem_arithmeticSubgroup_iff {σ : AlgebraInvolution ℚ A} {K : Subgroup σ.FiniteAdelicPoints}
    {g : σ.FiniteAdelicPoints} {γ : σ.similitudes} :
    γ ∈ arithmeticSubgroup σ K g ↔ g⁻¹ * σ.finiteAdelicDiagonal γ * g ∈ K := by
  constructor
  · rintro ⟨k, hk, hkγ⟩
    change g * k * g⁻¹ = σ.finiteAdelicDiagonal γ at hkγ
    have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    rw [← hkγ, e]
    exact hk
  · intro h
    refine ⟨g⁻¹ * σ.finiteAdelicDiagonal γ * g, h, ?_⟩
    change g * (g⁻¹ * σ.finiteAdelicDiagonal γ * g) * g⁻¹ = _
    group

/-- For an involution whose real scalar extension is positive and a compact subgroup `K` of the
finite adelic points, the arithmetic subgroup `GJ(ℚ) ∩ g K g⁻¹` is finite. -/
theorem finite_arithmeticSubgroup (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) {K : Subgroup σ.FiniteAdelicPoints}
    (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) (g : σ.FiniteAdelicPoints) :
    (arithmeticSubgroup σ K g : Set σ.similitudes).Finite := by
  have hc : Continuous ((MulAut.conj g).toMonoidHom :
      σ.FiniteAdelicPoints → σ.FiniteAdelicPoints) := by
    change Continuous fun x => g * x * g⁻¹
    fun_prop
  have hH : IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup σ.FiniteAdelicPoints) :
      Set σ.FiniteAdelicPoints) := by
    rw [Subgroup.coe_map]
    exact hK.image hc
  exact finite_comap_finiteAdelicDiagonal σ hpos hH

/-- For an involution whose real scalar extension is positive, every rational similitude lying
in a conjugate `g K g⁻¹` of a compact subgroup `K` of the finite adelic points has finite
order. -/
theorem isOfFinOrder_of_conj_mem (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) {K : Subgroup σ.FiniteAdelicPoints}
    (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) (g : σ.FiniteAdelicPoints)
    (γ : σ.similitudes) (hγ : g⁻¹ * σ.finiteAdelicDiagonal γ * g ∈ K) : IsOfFinOrder γ := by
  have : Finite (arithmeticSubgroup σ K g) :=
    (finite_arithmeticSubgroup σ hpos hK g).to_subtype
  exact (arithmeticSubgroup σ K g).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨γ, mem_arithmeticSubgroup_iff.2 hγ⟩ : arithmeticSubgroup σ K g))

end Langlands.Shimura.AlgebraInvolution
