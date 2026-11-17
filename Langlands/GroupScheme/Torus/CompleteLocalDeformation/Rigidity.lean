import Langlands.Algebra.GroupAlgebraCoaction

/-! # Rigidity of bialgebra maps to group algebras modulo an ideal

Two bialgebra maps `π π' : A → K[N]` whose coefficients agree modulo an ideal `I` agree
modulo every power of `I`, provided `A` is cocommutative modulo `I`. If `K` is `I`-adically
separated, the two maps are equal. -/

noncomputable section

universe u v w

open TensorProduct Coalgebra

namespace Langlands.GroupScheme.CompleteLocalDeformation

open Langlands.GroupAlgebraCoaction

section Coalgebra

variable {K : Type u} [CommRing K] {A : Type v} [AddCommGroup A] [Module K A] [Coalgebra K A]

/-- Convolution is evaluation of the first form after the right action of the second. -/
theorem conv_eq_comp_ract (f g : A →ₗ[K] K) : conv f g = f ∘ₗ ract g := by
  ext a
  let 𝓡 := Repr.arbitrary K a
  rw [conv_apply 𝓡, LinearMap.comp_apply, ract_apply 𝓡, map_sum]
  simp [mul_comm]

/-- Convolution of linear forms is associative. -/
theorem conv_assoc (f g h : A →ₗ[K] K) : conv (conv f g) h = conv f (conv g h) := by
  ext a
  simp only [conv_eq_comp_ract, LinearMap.comp_apply, ract_ract]

theorem conv_add_left (f g h : A →ₗ[K] K) : conv (f + g) h = conv f h + conv g h := by
  ext a
  let 𝓡 := Repr.arbitrary K a
  simp [conv_apply 𝓡, add_mul, Finset.sum_add_distrib]

theorem conv_add_right (f g h : A →ₗ[K] K) : conv f (g + h) = conv f g + conv f h := by
  ext a
  let 𝓡 := Repr.arbitrary K a
  simp [conv_apply 𝓡, mul_add, Finset.sum_add_distrib]

theorem conv_sub_left (f g h : A →ₗ[K] K) : conv (f - g) h = conv f h - conv g h := by
  ext a
  let 𝓡 := Repr.arbitrary K a
  simp [conv_apply 𝓡, sub_mul, Finset.sum_sub_distrib]

theorem conv_sub_right (f g h : A →ₗ[K] K) : conv f (g - h) = conv f g - conv f h := by
  ext a
  let 𝓡 := Repr.arbitrary K a
  simp [conv_apply 𝓡, mul_sub, Finset.sum_sub_distrib]

theorem conv_smul_right (f g : A →ₗ[K] K) (c : K) : conv f (c • g) = c • conv f g := by
  ext a
  let 𝓡 := Repr.arbitrary K a
  simp [conv_apply 𝓡, Finset.mul_sum, mul_left_comm]

/-- A linear form takes all its values in the ideal `J`. -/
def ValuesIn (J : Ideal K) (f : A →ₗ[K] K) : Prop := ∀ a, f a ∈ J

omit [Coalgebra K A] in
theorem ValuesIn.add {J : Ideal K} {f g : A →ₗ[K] K} (hf : ValuesIn J f) (hg : ValuesIn J g) :
    ValuesIn J (f + g) := fun a => J.add_mem (hf a) (hg a)

omit [Coalgebra K A] in
theorem ValuesIn.sub {J : Ideal K} {f g : A →ₗ[K] K} (hf : ValuesIn J f) (hg : ValuesIn J g) :
    ValuesIn J (f - g) := fun a => J.sub_mem (hf a) (hg a)

omit [Coalgebra K A] in
theorem ValuesIn.smul {J : Ideal K} {f : A →ₗ[K] K} (hf : ValuesIn J f) (c : K) :
    ValuesIn J (c • f) := fun a => J.mul_mem_left c (hf a)

omit [Coalgebra K A] in
theorem ValuesIn.mono {J J' : Ideal K} {f : A →ₗ[K] K} (hf : ValuesIn J f) (h : J ≤ J') :
    ValuesIn J' f := fun a => h (hf a)

theorem ValuesIn.conv_mul {J J' : Ideal K} {f g : A →ₗ[K] K} (hf : ValuesIn J f)
    (hg : ValuesIn J' g) : ValuesIn (J * J') (conv f g) := by
  intro a
  let 𝓡 := Repr.arbitrary K a
  rw [conv_apply 𝓡]
  exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_mul (hf _) (hg _)

theorem ValuesIn.conv_left {J : Ideal K} {f : A →ₗ[K] K} (hf : ValuesIn J f) (g : A →ₗ[K] K) :
    ValuesIn J (conv f g) := by
  intro a
  let 𝓡 := Repr.arbitrary K a
  rw [conv_apply 𝓡]
  exact Submodule.sum_mem _ fun i _ => J.mul_mem_right _ (hf _)

theorem ValuesIn.conv_right {J : Ideal K} {g : A →ₗ[K] K} (hg : ValuesIn J g) (f : A →ₗ[K] K) :
    ValuesIn J (conv f g) := by
  intro a
  let 𝓡 := Repr.arbitrary K a
  rw [conv_apply 𝓡]
  exact Submodule.sum_mem _ fun i _ => J.mul_mem_left _ (hg _)

/-- The tensor evaluation of two forms. -/
private def evalPair (f g : A →ₗ[K] K) : A ⊗[K] A →ₗ[K] K :=
  (TensorProduct.lid K K).toLinearMap ∘ₗ TensorProduct.map f g

omit [Coalgebra K A] in
private theorem evalPair_comm (f g : A →ₗ[K] K) (t : A ⊗[K] A) :
    evalPair g f t = evalPair f g (TensorProduct.comm K A A t) := by
  induction t with
  | tmul x y => simp [evalPair, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Coalgebra K A] in
private theorem evalPair_mem {J : Ideal K} {f : A →ₗ[K] K} (hf : ValuesIn J f)
    (g : A →ₗ[K] K) (t : A ⊗[K] A) : evalPair f g t ∈ J := by
  induction t with
  | tmul x y => simpa [evalPair] using J.mul_mem_right (g y) (hf x)
  | add x y hx hy => rw [map_add]; exact J.add_mem hx hy

/-- If the coalgebra is cocommutative modulo `I` and `f` takes values in `J`, then the two
convolutions of `f` and `g` agree modulo `I * J`. -/
theorem ValuesIn.conv_sub_conv_comm {I J : Ideal K}
    (hcomm : ∀ a : A, comul a - TensorProduct.comm K A A (comul a) ∈
      I • (⊤ : Submodule K (A ⊗[K] A)))
    {f : A →ₗ[K] K} (hf : ValuesIn J f) (g : A →ₗ[K] K) :
    ValuesIn (I * J) (conv f g - conv g f) := by
  intro a
  have h1 : conv f g a = evalPair f g (comul a) := rfl
  have h2 : conv g f a = evalPair f g (TensorProduct.comm K A A (comul a)) := by
    rw [← evalPair_comm]; rfl
  rw [LinearMap.sub_apply, h1, h2, ← map_sub]
  have hmem := hcomm a
  refine Submodule.smul_induction_on hmem ?_ ?_
  · intro r hr t _
    rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_mul hr (evalPair_mem hf g t)
  · intro x y hx hy
    rw [map_add]
    exact Ideal.add_mem _ hx hy

end Coalgebra

section Bialgebra

variable {K : Type u} [CommRing K] {N : Type w} [AddCommGroup N]
variable {A : Type v} [CommRing A] [Bialgebra K A]

/-- **Rigidity modulo powers.** If `A` is cocommutative modulo `I` and the coefficients of two
bialgebra maps `A → K[N]` agree modulo `I`, they agree modulo every power of `I`. -/
theorem coeff_sub_mem_pow (I : Ideal K)
    (hcomm : ∀ a : A, comul a - TensorProduct.comm K A A (comul a) ∈
      I • (⊤ : Submodule K (A ⊗[K] A)))
    (π π' : A →ₐc[K] AddMonoidAlgebra K N)
    (h : ∀ (a : A) (n : N), (π a).coeff n - (π' a).coeff n ∈ I) :
    ∀ (k : ℕ) (a : A) (n : N), (π a).coeff n - (π' a).coeff n ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
    intro a n
    set f := coeffForm π n with hfdef
    set g := coeffForm π' n with hgdef
    have hff : conv f f = f := by rw [hfdef, conv_coeffForm]; simp
    have hgg : conv g g = g := by rw [hgdef, conv_coeffForm]; simp
    set d := f - g with hddef
    have hd : ValuesIn (I ^ (k + 1)) d := fun b => by
      simpa [d, f, g] using ih b n
    -- the target ideal
    set J' := I ^ (k + 1 + 1)
    -- (1) `d = conv d f + conv g d`
    have h1 : d = conv d f + conv g d := by
      have : conv f f - conv g g = conv d f + conv g d := by
        rw [hddef, conv_sub_left, conv_sub_right]; abel
      rw [← this, hff, hgg]
    -- (2) `conv d f - conv d g = conv d d`
    have h2 : ValuesIn J' (conv d f - conv d g) := by
      have : conv d f - conv d g = conv d d := by rw [hddef, conv_sub_right]
      rw [this]
      refine (hd.conv_mul hd).mono ?_
      rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)
    -- (3) `conv d g - conv g d` by cocommutativity modulo `I`
    have h3 : ValuesIn J' (conv d g - conv g d) := by
      refine (hd.conv_sub_conv_comm hcomm g).mono ?_
      rw [← pow_succ']
    set e := conv g d with hedef
    -- (4) `d - 2 e`
    have h4 : ValuesIn J' (d - (2 : K) • e) := by
      have : d - (2 : K) • e = (conv d f - conv d g) + (conv d g - conv g d) := by
        conv_lhs => rw [h1]
        rw [two_smul]; abel
      rw [this]; exact h2.add h3
    -- (5) `e ≡ 0`
    have h5 : ValuesIn J' e := by
      have hc := h4.conv_right g
      have : conv g (d - (2 : K) • e) = -e := by
        rw [conv_sub_right, conv_smul_right, hedef, ← conv_assoc, hgg, two_smul]
        abel
      rw [this] at hc
      intro b
      simpa using J'.neg_mem (hc b)
    -- (6) conclude
    have h6 : ValuesIn J' d := by
      have : d = (d - (2 : K) • e) + (2 : K) • e := by abel
      rw [this]; exact h4.add (h5.smul 2)
    simpa [d, f, g] using h6 a

/-- **Rigidity.** Over an `I`-adically separated base, bialgebra maps `A → K[N]` from a
coalgebra cocommutative modulo `I` are determined by their coefficients modulo `I`. -/
theorem eq_of_coeff_sub_mem (I : Ideal K) (hsep : ∀ x : K, (∀ k : ℕ, x ∈ I ^ k) → x = 0)
    (hcomm : ∀ a : A, comul a - TensorProduct.comm K A A (comul a) ∈
      I • (⊤ : Submodule K (A ⊗[K] A)))
    (π π' : A →ₐc[K] AddMonoidAlgebra K N)
    (h : ∀ (a : A) (n : N), (π a).coeff n - (π' a).coeff n ∈ I) : π = π' := by
  ext a n
  have := hsep _ fun k => Ideal.pow_le_pow_right (Nat.le_succ k)
    (coeff_sub_mem_pow I hcomm π π' h k a n)
  exact sub_eq_zero.mp this

end Bialgebra

end Langlands.GroupScheme.CompleteLocalDeformation
