import Langlands.LinearAlgebra.WeylDenominatorIdentity

/-! # The Weyl character formula from Freudenthal's recursion -/

noncomputable section

open Set Function AddMonoidAlgebra

namespace Langlands.LinearAlgebra.WeylCharacter

open DominantTriangular

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-! ### Convolution of `ℤ[M]` with functions `M → ℚ` -/

/-- The convolution `(f ⋆ h)(ν) = ∑_κ f(κ) h(ν - κ)` of an element of `ℤ[M]` with an
arbitrary function `M → ℚ`. -/
def conv (f : AddMonoidAlgebra ℤ M) (h : M → ℚ) (ν : M) : ℚ :=
  f.coeff.sum fun κ r => (r : ℚ) * h (ν - κ)

theorem conv_zero_left (h : M → ℚ) : conv 0 h = 0 := by
  funext ν
  simp [conv]

theorem conv_add_left (f g : AddMonoidAlgebra ℤ M) (h : M → ℚ) :
    conv (f + g) h = conv f h + conv g h := by
  funext ν
  simp only [conv, coeff_add, Pi.add_apply]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]

theorem conv_single (a : M) (r : ℤ) (h : M → ℚ) (ν : M) :
    conv (single a r) h ν = r * h (ν - a) := by
  simp [conv, coeff_single, Finsupp.sum_single_index]

theorem conv_sub_left (f g : AddMonoidAlgebra ℤ M) (h : M → ℚ) :
    conv (f - g) h = conv f h - conv g h := by
  rw [eq_sub_iff_add_eq, ← conv_add_left, sub_add_cancel]

theorem conv_zero_right (f : AddMonoidAlgebra ℤ M) : conv f (0 : M → ℚ) = 0 := by
  funext ν
  simp [conv]

theorem conv_add_right (f : AddMonoidAlgebra ℤ M) (h h' : M → ℚ) :
    conv f (h + h') = conv f h + conv f h' := by
  funext ν
  simp only [conv, Pi.add_apply, mul_add]
  exact Finsupp.sum_add

theorem conv_sub_right (f : AddMonoidAlgebra ℤ M) (h h' : M → ℚ) :
    conv f (h - h') = conv f h - conv f h' := by
  rw [eq_sub_iff_add_eq, ← conv_add_right, sub_add_cancel]

theorem conv_smul_right (f : AddMonoidAlgebra ℤ M) (q : ℚ) (h : M → ℚ) :
    conv f (q • h) = q • conv f h := by
  funext ν
  simp only [conv, Pi.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

theorem conv_sum_right {κ : Type*} (s : Finset κ) (f : AddMonoidAlgebra ℤ M)
    (h : κ → M → ℚ) : conv f (∑ i ∈ s, h i) = ∑ i ∈ s, conv f (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conv_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, conv_add_right, ih]

theorem conv_one (h : M → ℚ) : conv 1 h = h := by
  funext ν
  rw [one_def, conv_single, sub_zero, Int.cast_one, one_mul]

theorem conv_mul (f g : AddMonoidAlgebra ℤ M) (h : M → ℚ) :
    conv (f * g) h = conv f (conv g h) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, conv_zero_left, conv_zero_left]
  | add f f' hf hf' => rw [add_mul, conv_add_left, conv_add_left, hf, hf']
  | single a r =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp only [mul_zero, conv_zero_left, conv_zero_right]
    | add g g' hg hg' => rw [mul_add, conv_add_left, conv_add_left, conv_add_right, hg, hg']
    | single c s =>
      funext ν
      rw [single_mul_single, conv_single, conv_single, conv_single, sub_sub]
      push_cast
      ring

theorem conv_comm_mul (f g : AddMonoidAlgebra ℤ M) (h : M → ℚ) :
    conv f (conv g h) = conv g (conv f h) := by
  rw [← conv_mul, mul_comm, conv_mul]

theorem conv_coeff (f g : AddMonoidAlgebra ℤ M) :
    conv f (fun μ => (g.coeff μ : ℚ)) = fun ν => ((f * g).coeff ν : ℚ) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [conv_zero_left, zero_mul]; funext ν; simp
  | add f f' hf hf' =>
    rw [conv_add_left, hf, hf', add_mul]
    funext ν
    simp
  | single a r =>
    funext ν
    rw [conv_single, coeff_single_mul_apply, neg_add_eq_sub]
    push_cast
    rfl

theorem conv_one_sub_single (α : M) (h : M → ℚ) (ν : M) :
    conv (1 - single (-α) 1) h ν = h ν - h (ν + α) := by
  rw [conv_sub_left, Pi.sub_apply, conv_one, conv_single, sub_neg_eq_add, Int.cast_one, one_mul]

theorem conv_one_add_single (α : M) (h : M → ℚ) (ν : M) :
    conv (1 + single (-α) 1) h ν = h ν + h (ν + α) := by
  rw [conv_add_left, Pi.add_apply, conv_one, conv_single, sub_neg_eq_add, Int.cast_one, one_mul]

/-! ### Sums along root strings -/

theorem finsum_nat_eq_zero_add {f : ℕ → ℚ} (hf : (support f).Finite) :
    ∑ᶠ j, f j = f 0 + ∑ᶠ j, f (j + 1) := by
  obtain ⟨N, hN⟩ := hf.bddAbove
  have h1 : support f ⊆ ↑(Finset.range (N + 1)) := fun j hj => by
    rw [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (hN hj)
  have h2 : support (fun j => f (j + 1)) ⊆ ↑(Finset.range N) := fun j hj => by
    rw [Finset.coe_range, Set.mem_Iio]
    have := hN (show j + 1 ∈ support f from hj)
    omega
  rw [finsum_eq_sum_of_support_subset f h1, finsum_eq_sum_of_support_subset _ h2,
    Finset.sum_range_succ', add_comm]

/-- `S(α, T)(μ) = ∑_{j ≥ 1} T(μ + j α)`. -/
def stringSum (α : M) (T : M → ℚ) (μ : M) : ℚ :=
  ∑ᶠ j : ℕ, T (μ + (j + 1) • α)

theorem stringSum_eq {α : M} (hα : Injective fun n : ℕ => n • α) {T : M → ℚ}
    (hT : (support T).Finite) (μ : M) :
    stringSum α T μ = T (μ + α) + stringSum α T (μ + α) := by
  have hinj : Injective fun j : ℕ => μ + (j + 1) • α := fun j k hjk => by
    have := hα (add_left_cancel hjk)
    omega
  have hfin : (support fun j : ℕ => T (μ + (j + 1) • α)).Finite := by
    rw [show (fun j : ℕ => T (μ + (j + 1) • α)) = T ∘ fun j : ℕ => μ + (j + 1) • α from rfl,
      support_comp_eq_preimage]
    exact hT.preimage hinj.injOn
  rw [stringSum, finsum_nat_eq_zero_add hfin, stringSum, zero_add, one_smul]
  congr 1
  refine finsum_congr fun j => ?_
  congr 1
  simp only [add_smul, one_smul]
  abel

/-! ### The Laplacian, derivatives and the bilinear term -/

section Form

variable (F : M →ₗ[ℤ] M →ₗ[ℤ] ℚ)

/-- The Laplacian `e^μ ↦ F(μ, μ) e^μ`, on functions `M → ℚ`. -/
def lap (h : M → ℚ) (ν : M) : ℚ :=
  F ν ν * h ν

/-- The derivative `e^μ ↦ F(x, μ) e^μ` in the direction `x`, on functions `M → ℚ`. -/
def der (x : M) (h : M → ℚ) (ν : M) : ℚ :=
  F x ν * h ν

/-- The bilinear term `B(f, h)(ν) = ∑_κ f(κ) F(κ, ν - κ) h(ν - κ)`. -/
def bil (f : AddMonoidAlgebra ℤ M) (h : M → ℚ) (ν : M) : ℚ :=
  f.coeff.sum fun κ r => (r : ℚ) * (F κ (ν - κ) * h (ν - κ))

theorem bil_zero_left (h : M → ℚ) : bil F 0 h = 0 := by
  funext ν
  simp [bil]

theorem bil_add_left (f g : AddMonoidAlgebra ℤ M) (h : M → ℚ) :
    bil F (f + g) h = bil F f h + bil F g h := by
  funext ν
  simp only [bil, coeff_add, Pi.add_apply]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]

theorem bil_single (a : M) (r : ℤ) (h : M → ℚ) :
    bil F (single a r) h = conv (single a r) (der F a h) := by
  funext ν
  rw [conv_single]
  simp [bil, der, coeff_single, Finsupp.sum_single_index]

theorem bil_sub_left (f g : AddMonoidAlgebra ℤ M) (h : M → ℚ) :
    bil F (f - g) h = bil F f h - bil F g h := by
  rw [eq_sub_iff_add_eq, ← bil_add_left, sub_add_cancel]

theorem bil_one (h : M → ℚ) : bil F 1 h = 0 := by
  rw [one_def, bil_single]
  funext ν
  simp [conv_single, der]

theorem der_neg (x : M) (h : M → ℚ) : der F (-x) h = -der F x h := by
  funext ν
  simp [der]

theorem der_add (x y : M) (h : M → ℚ) : der F (x + y) h = der F x h + der F y h := by
  funext ν
  simp [der, add_mul]

theorem der_sum {κ : Type*} (s : Finset κ) (x : κ → M) (h : M → ℚ) :
    der F (∑ i ∈ s, x i) h = ∑ i ∈ s, der F (x i) h := by
  funext ν
  simp [der, Finset.sum_mul]

theorem der_nsmul (n : ℕ) (x : M) (h : M → ℚ) : der F (n • x) h = (n : ℚ) • der F x h := by
  funext ν
  simp [der, mul_assoc]

theorem bil_one_sub_single (α : M) (h : M → ℚ) :
    bil F (1 - single (-α) 1) h = conv (single (-α) 1) (der F α h) := by
  rw [bil_sub_left, bil_one, bil_single, der_neg]
  funext ν
  simp [conv_single]

/-- The Leibniz rule for the bilinear term. -/
theorem bil_mul (f g : AddMonoidAlgebra ℤ M) (h : M → ℚ) :
    bil F (f * g) h = conv f (bil F g h) + conv g (bil F f h) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp only [zero_mul, bil_zero_left, conv_zero_left, conv_zero_right, add_zero]
  | add f f' hf hf' =>
    rw [add_mul, bil_add_left, bil_add_left, hf, hf', conv_add_left, conv_add_right]
    abel
  | single a r =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp only [mul_zero, bil_zero_left, conv_zero_left, conv_zero_right, add_zero]
    | add g g' hg hg' =>
      rw [mul_add, bil_add_left, bil_add_left, hg, hg', conv_add_left, conv_add_right]
      abel
    | single c s =>
      funext ν
      rw [single_mul_single, bil_single, bil_single, bil_single, Pi.add_apply, conv_single,
        conv_single, conv_single, conv_single, conv_single]
      simp only [der, sub_sub, map_add, LinearMap.add_apply]
      rw [add_comm c a]
      push_cast
      ring

variable {F}

/-- The product rule for the Laplacian, when `F(κ, κ)` is constant on the support of `f`. -/
theorem lap_conv (hF : ∀ x y, F x y = F y x) {f : AddMonoidAlgebra ℤ M} {r : ℚ}
    (hf : ∀ κ, f.coeff κ ≠ 0 → F κ κ = r) (h : M → ℚ) :
    lap F (conv f h) = r • conv f h + conv f (lap F h) + (2 : ℚ) • bil F f h := by
  funext ν
  simp only [lap, conv, bil, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finsupp.sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  have e : F (κ + (ν - κ)) (κ + (ν - κ)) =
      F κ κ + 2 * F κ (ν - κ) + F (ν - κ) (ν - κ) := by
    simp only [map_add, LinearMap.add_apply]
    rw [hF (ν - κ) κ]
    ring
  rw [add_sub_cancel, hf κ (Finsupp.mem_support_iff.mp hκ)] at e
  rw [e]
  ring

end Form

/-! ### Telescoping along root strings -/

section Telescope

variable {F : M →ₗ[ℤ] M →ₗ[ℤ] ℚ}

/-- Multiplying the two root-string sums of `±α` by `1 - e^{-α}` telescopes. -/
theorem conv_one_sub_single_stringSum (hF : ∀ x y, F x y = F y x) {α : M}
    (hα : Injective fun n : ℕ => n • α) (hα' : Injective fun n : ℕ => n • (-α))
    {χ : M → ℚ} (hχ : (support χ).Finite) :
    conv (1 - single (-α) 1) (stringSum α (fun κ => F κ α * χ κ) +
        stringSum (-α) (fun κ => F κ (-α) * χ κ)) =
      conv (1 + single (-α) 1) (der F α χ) := by
  have hT : ∀ x : M, (support fun κ => F κ x * χ κ).Finite := fun x =>
    hχ.subset (support_mul_subset_right _ _)
  funext ν
  rw [conv_one_sub_single, conv_one_add_single]
  simp only [Pi.add_apply]
  have e1 := stringSum_eq hα (hT α) ν
  have e2 := stringSum_eq hα' (hT (-α)) (ν + α)
  rw [add_neg_cancel_right] at e2
  rw [e1, e2]
  simp only [der, map_neg]
  rw [hF ν α, hF (ν + α) α]
  ring

theorem two_smul_conv_single_add (α : M) (d : M → ℚ) :
    (2 : ℚ) • conv (single (-α) 1) d + conv (1 - single (-α) 1) d =
      conv (1 + single (-α) 1) d := by
  funext ν
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, conv_single, conv_one_sub_single,
    conv_one_add_single, sub_neg_eq_add, Int.cast_one]
  ring

/-- The key identity behind the Weyl character formula, for a product
`Q = ∏_{i ∈ s} (1 - e^{-α_i})`: `2 B(Q, h) + Q ⋆ ∑_i ∂_{α_i} h = Q ⋆ ∑_i U_i` whenever
`(1 - e^{-α_i}) ⋆ U_i = (1 + e^{-α_i}) ⋆ ∂_{α_i} h` for every `i ∈ s`. -/
theorem two_smul_bil_prod {κ : Type*} (s : Finset κ) (α : κ → M) (h : M → ℚ)
    (U : κ → M → ℚ)
    (hU : ∀ i ∈ s, conv (1 - single (-α i) 1) (U i) = conv (1 + single (-α i) 1) (der F (α i) h)) :
    (2 : ℚ) • bil F (∏ i ∈ s, (1 - single (-α i) 1)) h +
        conv (∏ i ∈ s, (1 - single (-α i) 1)) (∑ i ∈ s, der F (α i) h) =
      conv (∏ i ∈ s, (1 - single (-α i) 1)) (∑ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, bil_one, conv_zero_right, smul_zero,
      add_zero]
  | insert a s ha ih =>
    have ih := ih fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have hUa := hU a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    set Q := ∏ i ∈ s, (1 - single (-α i) 1 : AddMonoidAlgebra ℤ M)
    set E := (1 - single (-α a) 1 : AddMonoidAlgebra ℤ M)
    rw [bil_mul, bil_one_sub_single, conv_add_right (E * Q), conv_add_right (E * Q)]
    simp only [conv_mul E Q]
    rw [← ih, conv_comm_mul E Q (U a), hUa, ← two_smul_conv_single_add, conv_add_right Q,
      conv_smul_right Q, conv_add_right E, conv_smul_right E,
      conv_comm_mul E Q (der F (α a) h), smul_add]
    abel

/-- The identity `2 B(e^ρ Q, h) = e^ρ Q ⋆ ∑_i U_i` when `2 ρ = ∑_{i ∈ s} α_i`. -/
theorem two_smul_bil_denominator {κ : Type*} (s : Finset κ) (α : κ → M) (ρ : M)
    (hρ : 2 • ρ = ∑ i ∈ s, α i) (h : M → ℚ) (U : κ → M → ℚ)
    (hU : ∀ i ∈ s, conv (1 - single (-α i) 1) (U i) = conv (1 + single (-α i) 1) (der F (α i) h)) :
    (2 : ℚ) • bil F (single ρ 1 * ∏ i ∈ s, (1 - single (-α i) 1)) h =
      conv (single ρ 1 * ∏ i ∈ s, (1 - single (-α i) 1)) (∑ i ∈ s, U i) := by
  have key := two_smul_bil_prod s α h U hU
  have h2 : (2 : ℚ) • der F ρ h = ∑ i ∈ s, der F (α i) h := by
    rw [← der_sum, ← hρ, der_nsmul]
    norm_num
  rw [bil_mul, bil_single, conv_mul, ← key, smul_add, ← conv_smul_right, ← conv_smul_right,
    ← conv_smul_right, h2, conv_comm_mul (∏ i ∈ s, (1 - single (-α i) 1)) (single ρ 1), ← conv_add_right]

end Telescope

/-! ### Invariant forms and the reflection group -/

section Main

variable {P : RootPairing ι ℤ M N} (b : P.Base) {F : M →ₗ[ℤ] M →ₗ[ℤ] ℚ}

theorem apply_eq_of_mem_reflectionGroup {α : Type*} {g : M → α}
    (hg : ∀ i x, g (P.reflection i x) = g x) {w : M ≃ₗ[ℤ] M} (hw : w ∈ reflectionGroup P) :
    ∀ x, g (w x) = g x := by
  induction hw using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact hg i
  | one => exact fun x => rfl
  | mul u v _ _ hu hv => exact fun x => (hu (v x)).trans (hv x)
  | inv u _ hu =>
    intro x
    change g (u.symm x) = g x
    rw [← hu (u.symm x), LinearEquiv.apply_symm_apply]

theorem form_apply_eq_of_mem_reflectionGroup
    (hF : ∀ i x y, F (P.reflection i x) (P.reflection i y) = F x y) {w : M ≃ₗ[ℤ] M}
    (hw : w ∈ reflectionGroup P) : ∀ x y, F (w x) (w y) = F x y := by
  induction hw using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact hF i
  | one => exact fun x y => rfl
  | mul u v _ _ hu hv => exact fun x y => (hu (v x) (v y)).trans (hv x y)
  | inv u _ hu =>
    intro x y
    change F (u.symm x) (u.symm y) = F x y
    rw [← hu (u.symm x) (u.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- For a reflection-invariant form, `F(α, α) ⟨x, α^∨⟩ = 2 F(α, x)`. -/
theorem form_root_mul_pairing (hF : ∀ i x y, F (P.reflection i x) (P.reflection i y) = F x y)
    (i : ι) (x : M) :
    F (P.root i) (P.root i) * (P.toLinearMap x (P.coroot i) : ℚ) = 2 * F (P.root i) x := by
  have h := hF i (P.root i) x
  rw [RootPairing.reflection_apply_self, RootPairing.reflection_apply] at h
  simp only [map_neg, map_sub, map_zsmul, LinearMap.neg_apply, zsmul_eq_mul] at h
  change F (P.root i) (P.root i) * (P.coroot' i x : ℚ) = _
  linarith

theorem form_nonneg_of_mem_positiveCone (hFs : ∀ x y, F x y = F y x)
    (hF : ∀ i x y, F (P.reflection i x) (P.reflection i y) = F x y)
    (hpos : ∀ x, x ≠ 0 → 0 < F x x) {ν d : M} (hν : IsDominant P b ν)
    (hd : d ∈ positiveCone P b) : 0 ≤ F ν d := by
  induction hd using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have h1 := form_root_mul_pairing hF a ν
    have h2 := hpos _ (P.ne_zero a)
    have h3 : (0 : ℚ) ≤ (P.toLinearMap ν (P.coroot a) : ℚ) := by exact_mod_cast hν a
    rw [hFs]
    nlinarith
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_nonneg hy hz

theorem form_lt_of_mem_positiveCone (hFs : ∀ x y, F x y = F y x)
    (hF : ∀ i x y, F (P.reflection i x) (P.reflection i y) = F x y)
    (hpos : ∀ x, x ≠ 0 → 0 < F x x) {ν d : M} (hν : IsDominant P b ν)
    (hd : d ∈ positiveCone P b) (hd0 : d ≠ 0) : F ν ν < F (ν + d) (ν + d) := by
  have h1 := form_nonneg_of_mem_positiveCone b hFs hF hpos hν hd
  have h2 := hpos d hd0
  simp only [map_add, LinearMap.add_apply]
  rw [hFs d ν]
  linarith

theorem exists_eq_of_coeff_alternant_ne_zero [Finite ι] {ν κ : M}
    (h : (alternant P ν).coeff κ ≠ 0) : ∃ w ∈ reflectionGroup P, w ν = κ := by
  classical
  let _ : Fintype (reflectionGroup P) := Fintype.ofFinite _
  rw [alternant_eq_sum, coeff_sum, Finsupp.finsetSum_apply] at h
  obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_single, Finsupp.single_apply] at hw
  exact ⟨w, w.2, by_contra fun hne => hw (ite_eq_right hne)⟩

/-! ### Roots: injectivity of multiples, dominance and negatives -/

theorem nsmul_root_injective (i : ι) : Injective fun n : ℕ => n • P.root i := by
  intro m n h
  have := congrArg (fun x => P.toLinearMap x (P.coroot i)) h
  simp only [map_nsmul, LinearMap.smul_apply, RootPairing.root_coroot_two, nsmul_eq_mul] at this
  omega

theorem nsmul_neg_root_injective (i : ι) : Injective fun n : ℕ => n • (-P.root i) := by
  intro m n h
  simp only [smul_neg, neg_inj] at h
  exact nsmul_root_injective i h

theorem isDominant_of_invariant {c : M →₀ ℤ} {lam : M}
    (hinv : ∀ i μ, c (P.reflection i μ) = c μ) (hlam : c lam ≠ 0)
    (hbelow : ∀ μ, c μ ≠ 0 → lam - μ ∈ positiveCone P b) : IsDominant P b lam := by
  intro a
  have h := hbelow _ (by rw [hinv]; exact hlam : c (P.reflection a lam) ≠ 0)
  rw [RootPairing.reflection_apply, sub_sub_cancel] at h
  change 0 ≤ P.coroot' a lam
  by_contra hneg
  rw [not_le] at hneg
  have h2 : -(P.coroot' a lam • P.root a) ∈ positiveCone P b := by
    rw [← neg_smul, ← Int.toNat_of_nonneg (by omega : 0 ≤ -P.coroot' a lam), natCast_zsmul]
    exact nsmul_mem (root_mem_positiveCone P b a) _
  have h3 := eq_zero_of_mem_positiveCone_of_neg_mem P b h h2
  have := congrArg (fun x => P.toLinearMap x (P.coroot a)) h3
  simp only [map_zsmul, LinearMap.smul_apply, RootPairing.root_coroot_two, smul_eq_mul,
    map_zero, LinearMap.zero_apply] at this
  change P.coroot' a lam * 2 = 0 at this
  omega

variable (P) in
/-- The index of the negative of the root `α_i`. -/
def negIdx (i : ι) : ι :=
  P.reflectionPerm i i

theorem root_negIdx (i : ι) : P.root (negIdx P i) = -P.root i := by
  rw [negIdx, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]

theorem negIdx_negIdx (i : ι) : negIdx P (negIdx P i) = i :=
  P.root.injective (by rw [root_negIdx, root_negIdx, neg_neg])

variable [Fintype ι]

theorem finsum_posRoots {A : Type*} [AddCommMonoid A] (f : ι → A) :
    ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), f i = ∑ i ∈ posRoots b, f i := by
  classical
  rw [posRoots, Finset.sum_filter, ← finsum_eq_sum_of_fintype]
  exact finsum_congr fun i => finsum_eq_if

theorem sum_eq_sum_posRoots_add_negIdx {A : Type*} [AddCommMonoid A] (V : ι → A) :
    ∑ i, V i = ∑ i ∈ posRoots b, (V i + V (negIdx P i)) := by
  classical
  rw [Finset.sum_add_distrib, ← Finset.sum_sdiff (Finset.subset_univ (posRoots b)), add_comm]
  congr 1
  refine Finset.sum_nbij' (negIdx P) (negIdx P) (fun i hi => ?_) (fun i hi => ?_)
    (fun i _ => negIdx_negIdx i) (fun i _ => negIdx_negIdx i)
    (fun i _ => by rw [negIdx_negIdx])
  · rw [Finset.mem_sdiff, mem_posRoots] at hi
    rw [mem_posRoots, root_negIdx]
    exact (root_mem_or_neg_mem b i).resolve_left hi.2
  · rw [Finset.mem_sdiff, mem_posRoots, root_negIdx]
    exact ⟨Finset.mem_univ _, neg_root_notMem_of_mem b ((mem_posRoots b).mp hi)⟩

/-! ### The main theorem -/

variable [P.IsReduced] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- **The Weyl character formula from Freudenthal's recursion.** Let `F` be a symmetric,
reflection-invariant, positive definite `ℚ`-valued form on `M`, let `2 ρ` be the sum of the
positive roots, and let `c : M →₀ ℤ` be reflection invariant, with `c(λ) = 1`, support below
`λ`, and satisfying Freudenthal's recursion
`(F(λ, λ) + ∑_{α > 0} F(λ, α) - F(μ, μ)) c(μ) = ∑_{α} ∑_{j ≥ 1} F(μ + j α, α) c(μ + j α)`.
Then `J(ρ) · ∑_μ c(μ) e^μ = J(λ + ρ)`. -/
theorem alternant_mul_ofCoeff_eq (hFs : ∀ x y, F x y = F y x)
    (hF : ∀ i x y, F (P.reflection i x) (P.reflection i y) = F x y)
    (hpos : ∀ x, x ≠ 0 → 0 < F x x) {ρ : M}
    (hρ : 2 • ρ = ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), P.root i)
    (c : M →₀ ℤ) (lam : M) (hinv : ∀ i μ, c (P.reflection i μ) = c μ) (hlam : c lam = 1)
    (hbelow : ∀ μ, c μ ≠ 0 → lam - μ ∈ positiveCone P b)
    (hfreud : ∀ μ, (F lam lam + ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), F lam (P.root i) -
        F μ μ) * (c μ : ℚ) =
      ∑ᶠ (i : ι) (j : ℕ), F (μ + (j + 1) • P.root i) (P.root i) *
        (c (μ + (j + 1) • P.root i) : ℚ)) :
    alternant P ρ * ofCoeff c = alternant P (lam + ρ) := by
  classical
  let χ : M → ℚ := fun μ => (c μ : ℚ)
  let c0 : ℚ := F lam lam + ∑ i ∈ posRoots b, F lam (P.root i)
  have hχfin : (support χ).Finite := by
    refine c.support.finite_toSet.subset fun μ hμ => ?_
    simp only [Function.mem_support, χ, ne_eq, Int.cast_eq_zero] at hμ
    exact Finsupp.mem_support_iff.mpr hμ
  -- The root-string sums of Freudenthal's recursion, paired by `±α`.
  let V : ι → M → ℚ := fun i => stringSum (P.root i) (fun κ => F κ (P.root i) * χ κ)
  let U : ι → M → ℚ := fun i => V i + V (negIdx P i)
  have hU : ∀ i ∈ posRoots b, conv (1 - single (-P.root i) 1) (U i) =
      conv (1 + single (-P.root i) 1) (der F (P.root i) χ) := by
    intro i _
    simp only [U, V, root_negIdx]
    exact conv_one_sub_single_stringSum hFs (nsmul_root_injective i)
      (nsmul_neg_root_injective i) hχfin
  have hsumU : ∑ i ∈ posRoots b, U i = c0 • χ - lap F χ := by
    funext μ
    have h := hfreud μ
    rw [finsum_posRoots b, finsum_eq_sum_of_fintype (α := ι),
      sum_eq_sum_posRoots_add_negIdx b] at h
    rw [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [lap]
    rw [← sub_mul]
    exact h.symm
  have h2ρ : 2 • ρ = ∑ i ∈ posRoots b, P.root i := by rw [hρ, finsum_posRoots b]
  -- The Laplacian identity for `D χ`.
  have hD : denominator b ρ = alternant P ρ := denominator_eq_alternant b hρ
  have hDF : ∀ κ, (denominator b ρ).coeff κ ≠ 0 → F κ κ = F ρ ρ := by
    intro κ hκ
    rw [hD] at hκ
    obtain ⟨w, hw, rfl⟩ := exists_eq_of_coeff_alternant_ne_zero hκ
    exact form_apply_eq_of_mem_reflectionGroup hF hw ρ ρ
  have hbil : (2 : ℚ) • bil F (denominator b ρ) χ =
      conv (denominator b ρ) (∑ i ∈ posRoots b, U i) :=
    two_smul_bil_denominator (posRoots b) P.root ρ h2ρ χ U hU
  have key : lap F (conv (denominator b ρ) χ) = (F ρ ρ + c0) • conv (denominator b ρ) χ := by
    rw [lap_conv hFs hDF χ, hbil, hsumU, conv_sub_right, conv_smul_right]
    simp only [c0, add_smul]
    abel
  have hc0 : F ρ ρ + c0 = F (lam + ρ) (lam + ρ) := by
    have : ∑ i ∈ posRoots b, F lam (P.root i) = 2 * F lam ρ := by
      rw [← map_sum, ← h2ρ, map_nsmul, nsmul_eq_mul]
      norm_num
    simp only [c0, this, map_add, LinearMap.add_apply]
    rw [hFs ρ lam]
    ring
  set g := denominator b ρ * ofCoeff c with hgdef
  have hχg : conv (denominator b ρ) χ = fun ν => (g.coeff ν : ℚ) :=
    conv_coeff (denominator b ρ) (ofCoeff c)
  have hg : ∀ ν, F ν ν * (g.coeff ν : ℚ) = F (lam + ρ) (lam + ρ) * g.coeff ν := by
    intro ν
    have := congrFun key ν
    rw [hχg, hc0] at this
    simpa [lap] using this
  -- `g` is alternating, below `λ + ρ`, with coefficient `1` there.
  have hact : ∀ w ∈ reflectionGroup P, act w (ofCoeff c) = ofCoeff c := by
    intro w hw
    ext μ
    rw [coeff_act, coeff_ofCoeff]
    exact apply_eq_of_mem_reflectionGroup hinv (inv_mem hw) μ
  have hgalt : IsAlternating P g := by
    intro w hw
    rw [hgdef, map_mul, isAlternating_denominator b hρ w hw, hact w hw, smul_mul_assoc]
  have hcbelow : IsBelow b (ofCoeff c) lam := fun μ hμ => hbelow μ hμ
  have hgbelow : IsBelow b g (ρ + lam) := (isBelow_denominator b ρ).1.mul hcbelow
  have hg1 : g.coeff (lam + ρ) = 1 := by
    rw [add_comm, hgdef, (isBelow_denominator b ρ).1.coeff_mul hcbelow,
      (isBelow_denominator b ρ).2, coeff_ofCoeff, hlam, one_mul]
  have hdom := isDominant_of_invariant b hinv (by rw [hlam]; exact one_ne_zero) hbelow
  have hstrict : IsStrictlyDominant b (lam + ρ) := fun a => by
    have h1 := hdom a
    have h2 := pairing_rho_eq_one b hρ a
    rw [map_add, LinearMap.add_apply, h2]
    omega
  have huniq : ∀ ν, IsStrictlyDominant b ν → g.coeff ν ≠ 0 → ν = lam + ρ := by
    intro ν hν hne
    have hle : lam + ρ - ν ∈ positiveCone P b := by
      rw [add_comm lam ρ]
      exact hgbelow ν hne
    by_contra hne'
    have hd0 : lam + ρ - ν ≠ 0 := sub_ne_zero.mpr (Ne.symm hne')
    have hlt := form_lt_of_mem_positiveCone b hFs hF hpos hν.isDominant hle hd0
    rw [add_sub_cancel] at hlt
    have hne'' : (g.coeff ν : ℚ) ≠ 0 := by exact_mod_cast hne
    have := mul_right_cancel₀ hne'' (hg ν)
    linarith
  rw [← hD]
  exact eq_alternant_of_isBelow b hgalt hstrict hg1 huniq

end Main

end Langlands.LinearAlgebra.WeylCharacter
