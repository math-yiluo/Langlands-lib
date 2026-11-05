import Langlands.Algebra.PTorsionHopf.AugmentationIdeal

/-! # Convolution of functionals on products of primitive elements -/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace Langlands.Algebra.PTorsionHopf

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Bialgebra k A] [IsCocomm k A]

omit [IsCocomm k A] in
theorem add_apply' (x y : WithConv (A →ₗ[k] k)) (b : A) : (x + y) b = x b + y b := rfl

omit [IsCocomm k A] in
/-- The comultiplication of a product of primitive elements. -/
theorem comul_prod_primitive {ι : Type*} [DecidableEq ι] (I : Finset ι) (y : ι → A)
    (hy : ∀ v ∈ I, Bialgebra.IsPrimitiveElem k (y v)) :
    comul (R := k) (∏ v ∈ I, y v) =
      ∑ T ∈ I.powerset, (∏ v ∈ T, y v) ⊗ₜ[k] (∏ v ∈ I \ T, y v) := by
  have h1 : comul (R := k) (∏ v ∈ I, y v) =
      ∏ v ∈ I, (y v ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] y v) := by
    rw [← Bialgebra.comulAlgHom_apply, map_prod]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [Bialgebra.comulAlgHom_apply, (hy v hv).comul_eq_tmul_add_tmul, add_comm]
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hl : ∏ v ∈ T, (y v ⊗ₜ[k] (1 : A)) = (∏ v ∈ T, y v) ⊗ₜ[k] (1 : A) := by
    have := (map_prod (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := A))
      y T).symm
    simpa only [Algebra.TensorProduct.includeLeft_apply] using this
  have hr : ∏ v ∈ I \ T, ((1 : A) ⊗ₜ[k] y v) = (1 : A) ⊗ₜ[k] (∏ v ∈ I \ T, y v) := by
    have := (map_prod (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := A))
      y (I \ T)).symm
    simpa only [Algebra.TensorProduct.includeRight_apply] using this
  rw [hl, hr, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [IsCocomm k A] in
/-- A convolution product evaluated on a product of primitive elements. -/
theorem convMul_apply_prod {ι : Type*} [DecidableEq ι] (I : Finset ι) (y : ι → A)
    (hy : ∀ v ∈ I, Bialgebra.IsPrimitiveElem k (y v)) (η Θ : WithConv (A →ₗ[k] k)) :
    (η * Θ) (∏ v ∈ I, y v) =
      ∑ T ∈ I.powerset, η (∏ v ∈ T, y v) * Θ (∏ v ∈ I \ T, y v) := by
  rw [LinearMap.convMul_apply, comul_prod_primitive I y hy, map_sum, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [TensorProduct.map_tmul, LinearMap.mul'_apply]

/-- Elements of the `n`-th power of the augmentation ideal kill products of fewer than `n`
primitive elements. -/
theorem apply_prod_eq_zero_of_card_lt {ι : Type*} [DecidableEq ι] (y : ι → A) (n : ℕ) :
    ∀ Θ ∈ augIdeal (k := k) (A := A) ^ n, ∀ I : Finset ι,
      (∀ v ∈ I, Bialgebra.IsPrimitiveElem k (y v)) → I.card < n → Θ (∏ v ∈ I, y v) = 0 := by
  induction n with
  | zero => intro Θ _ I _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro Θ hΘ
    rw [pow_succ' (augIdeal (k := k) (A := A)) n] at hΘ
    refine Submodule.mul_induction_on hΘ ?_ ?_
    · intro η hη Θ' hΘ' I hy hI
      rw [convMul_apply_prod I y hy]
      refine Finset.sum_eq_zero fun T hT => ?_
      rw [Finset.mem_powerset] at hT
      rcases T.eq_empty_or_nonempty with rfl | hne
      · rw [Finset.prod_empty, mem_augIdeal.1 hη, zero_mul]
      · have hlt : (I \ T).card < n := by
          have := Finset.card_lt_card (Finset.sdiff_ssubset hT hne)
          omega
        rw [ih Θ' hΘ' (I \ T) (fun v hv => hy v (Finset.sdiff_subset hv)) hlt, mul_zero]
    · intro x z hx hz I hy hI
      rw [add_apply', hx I hy hI, hz I hy hI, add_zero]

/-- **Leibniz expansion.** For `η` in the augmentation ideal and `Θ` in its `n`-th power, the
convolution evaluated on a product of `n + 1` primitive elements removes one factor at a time. -/
theorem convMul_apply_prod_eq_sum {ι : Type*} [DecidableEq ι] (y : ι → A) (I : Finset ι)
    (hy : ∀ v ∈ I, Bialgebra.IsPrimitiveElem k (y v)) {η Θ : WithConv (A →ₗ[k] k)}
    (hη : η ∈ augIdeal (k := k) (A := A)) {n : ℕ} (hΘ : Θ ∈ augIdeal (k := k) (A := A) ^ n)
    (hI : I.card = n + 1) :
    (η * Θ) (∏ v ∈ I, y v) = ∑ v ∈ I, η (y v) * Θ (∏ w ∈ I.erase v, y w) := by
  rw [convMul_apply_prod I y hy]
  rw [← Finset.sum_subset (s₁ := I.powersetCard 1)
    (fun T hT => Finset.mem_powerset.2 (Finset.mem_powersetCard.1 hT).1)]
  · rw [Finset.powersetCard_one, Finset.sum_map]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton,
      Finset.sdiff_singleton_eq_erase]
  · intro T hT hT1
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_powersetCard] at hT1
    rcases T.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.prod_empty, mem_augIdeal.1 hη, zero_mul]
    · have h2 : 2 ≤ T.card := by
        have := hne.card_pos
        have : T.card ≠ 1 := fun h => hT1 ⟨hT, h⟩
        omega
      have hlt : (I \ T).card < n := by
        have := Finset.card_le_card hT
        rw [Finset.card_sdiff_of_subset hT]
        omega
      rw [apply_prod_eq_zero_of_card_lt y n Θ hΘ (I \ T)
        (fun v hv => hy v (Finset.sdiff_subset hv)) hlt, mul_zero]

/-! ### Monomials in a dual system of primitive elements -/

section Kronecker

variable {r : ℕ}

/-- The number of indices in `I` carrying each label. -/
def labelCount {ι : Type*} (l : ι → Fin r) (I : Finset ι) : Fin r → ℕ :=
  fun i => (I.filter (fun v => l v = i)).card

theorem labelCount_erase {ι : Type*} [DecidableEq ι] (l : ι → Fin r) {I : Finset ι} {v : ι}
    (hv : v ∈ I) :
    labelCount l (I.erase v) = Function.update (labelCount l I) (l v) (labelCount l I (l v) - 1) := by
  funext j
  simp only [labelCount, Finset.filter_erase]
  by_cases hj : j = l v
  · subst hj
    rw [Function.update_self, Finset.card_erase_of_mem (s := I.filter (fun w => l w = l v))
      (Finset.mem_filter.2 ⟨hv, rfl⟩)]
  · rw [Function.update_of_ne hj,
      Finset.erase_eq_of_notMem fun h => hj (Finset.mem_filter.1 h).2.symm]
    rfl

theorem labelCount_empty {ι : Type*} (l : ι → Fin r) : labelCount l (∅ : Finset ι) = 0 :=
  funext fun _ => by simp [labelCount]

/-- A product of powers of elements of an ideal lies in the power by the total exponent. -/
theorem prod_pow_mem_pow_sum {R ι : Type*} [CommRing R] [DecidableEq ι] (I : Ideal R)
    (x : ι → R) (hx : ∀ i, x i ∈ I) (γ : ι → ℕ) (s : Finset ι) :
    ∏ i ∈ s, x i ^ γ i ∈ I ^ (∑ i ∈ s, γ i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hx a) _) ih

omit [IsCocomm k A] in
/-- The monomial `∏ ξᵢ ^ γᵢ` in the convolution dual. -/
def dualMonomial (ξ : Fin r → WithConv (A →ₗ[k] k)) (γ : Fin r → ℕ) :
    WithConv (A →ₗ[k] k) :=
  ∏ i, ξ i ^ γ i

theorem dualMonomial_mem {ξ : Fin r → WithConv (A →ₗ[k] k)}
    (hξ : ∀ i, ξ i ∈ augIdeal (k := k) (A := A)) (γ : Fin r → ℕ) :
    dualMonomial ξ γ ∈ augIdeal (k := k) (A := A) ^ (∑ i, γ i) := by
  exact prod_pow_mem_pow_sum _ ξ hξ γ Finset.univ

theorem dualMonomial_update (ξ : Fin r → WithConv (A →ₗ[k] k)) (γ : Fin r → ℕ) {i : Fin r}
    (hi : γ i ≠ 0) :
    dualMonomial ξ γ = ξ i * dualMonomial ξ (Function.update γ i (γ i - 1)) := by
  classical
  rw [dualMonomial, dualMonomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, ← mul_assoc,
    ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi)]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem factorial_update (γ : Fin r → ℕ) {i : Fin r} (hi : γ i ≠ 0) :
    ∏ j, (γ j).factorial = γ i * ∏ j, (Function.update γ i (γ i - 1) j).factorial := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, ← mul_assoc,
    Nat.mul_factorial_pred hi]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem sum_update (γ : Fin r → ℕ) {i : Fin r} (hi : γ i ≠ 0) :
    ∑ j, Function.update γ i (γ i - 1) j + 1 = ∑ j, γ j := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  have : ∑ j ∈ Finset.univ.erase i, Function.update γ i (γ i - 1) j =
      ∑ j ∈ Finset.univ.erase i, γ j :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this]
  omega

variable {b : Fin r → A} (hb : ∀ i, Bialgebra.IsPrimitiveElem k (b i))
  {ξ : Fin r → WithConv (A →ₗ[k] k)} (hξ : ∀ i, ξ i ∈ augIdeal (k := k) (A := A))
  (hξb : ∀ i j, ξ i (b j) = if i = j then 1 else 0)
include hb hξ hξb

/-- **Kronecker pairing.** A dual monomial evaluated on a product of primitive elements of the
dual system is `γ!` when the label counts are `γ`, and zero otherwise. -/
theorem dualMonomial_apply_prod {ι : Type*} [DecidableEq ι] (l : ι → Fin r) :
    ∀ (n : ℕ) (γ : Fin r → ℕ), ∑ i, γ i = n → ∀ I : Finset ι, I.card = n →
      dualMonomial ξ γ (∏ v ∈ I, b (l v)) =
        if labelCount l I = γ then ((∏ i, (γ i).factorial : ℕ) : k) else 0 := by
  intro n
  induction n with
  | zero =>
    intro γ hγ I hI
    have hγ0 : γ = 0 := funext fun i => (Finset.sum_eq_zero_iff.1 hγ) i (Finset.mem_univ i)
    have hI0 : I = ∅ := Finset.card_eq_zero.1 hI
    subst hγ0 hI0
    rw [ite_eq_left (labelCount_empty l)]
    simp [dualMonomial]
  | succ n ih =>
    intro γ hγ I hI
    obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hγ
    have hγ' : ∑ j, Function.update γ i (γ i - 1) j = n := by
      have := sum_update γ hi
      omega
    set γ' := Function.update γ i (γ i - 1) with hγ'def
    have hmem : dualMonomial ξ γ' ∈ augIdeal (k := k) (A := A) ^ n :=
      hγ' ▸ dualMonomial_mem hξ γ'
    rw [dualMonomial_update ξ γ hi, convMul_apply_prod_eq_sum (fun v => b (l v)) I
      (fun v _ => hb (l v)) (hξ i) hmem hI]
    set c : k := if Function.update (labelCount l I) i (labelCount l I i - 1) = γ' then
      ((∏ j, (γ' j).factorial : ℕ) : k) else 0 with hc
    have hterm : ∀ v ∈ I, ξ i (b (l v)) * dualMonomial ξ γ' (∏ w ∈ I.erase v, b (l w)) =
        if l v = i then c else 0 := by
      intro v hv
      rw [hξb, ih γ' hγ' (I.erase v) (by rw [Finset.card_erase_of_mem hv, hI]; rfl)]
      by_cases hvi : l v = i
      · rw [ite_eq_left hvi.symm, ite_eq_left hvi, one_mul, labelCount_erase l hv, hvi]
      · rw [ite_eq_right (Ne.symm hvi), ite_eq_right hvi, zero_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    change ((labelCount l I i : ℕ) : k) * c = _
    by_cases h : labelCount l I = γ
    · rw [ite_eq_left h, hc, ite_eq_left (by rw [h]), factorial_update γ hi, h, Nat.cast_mul]
    · rw [ite_eq_right h]
      by_cases hc0 : labelCount l I i = 0
      · rw [hc0, Nat.cast_zero, zero_mul]
      · rw [hc, ite_eq_right, mul_zero]
        intro heq
        apply h
        funext j
        have hj := congrFun heq j
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self, hγ'def, Function.update_self] at hj
          omega
        · rwa [Function.update_of_ne hji, hγ'def, Function.update_of_ne hji] at hj

end Kronecker

end Langlands.Algebra.PTorsionHopf
