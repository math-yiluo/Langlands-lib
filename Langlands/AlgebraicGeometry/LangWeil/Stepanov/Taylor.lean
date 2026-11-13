import Langlands.AlgebraicGeometry.LangWeil.Stepanov.Box

/-!
# Bivariate Taylor expansion and filtered ring homomorphisms

`theta P = P(X + U, Y + V)`, valued in `F[X][Y][U][V]` (outer variable `V`).
Its coefficient of `U^e₀ V^e₁` lies in the box `(a - e₀, b - e₁)` when `P` lies in
the box `(a, b)`; the coefficients at `U^0 V^k` are the Hasse derivatives in `Y`.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

/-- Shortcut instance: without it, instance search fails on four nested polynomial rings. -/
instance instCommRingPolyPoly (R : Type*) [CommRing R] : CommRing (Polynomial (Polynomial R)) :=
  inferInstance

variable {F : Type u} [CommRing F]

/-- A ring homomorphism out of `F[X][Y]` maps boxes into any multiplicative filtration
containing the images of the constants, of `X` and of `Y` in the right degrees. -/
theorem map_fil_of_inBox {A : Type*} [CommRing A] (φ : Polynomial (Polynomial F) →+* A)
    (Fil : ℤ → ℤ → A → Prop)
    (h0 : ∀ a b, Fil a b 0) (hadd : ∀ a b x y, Fil a b x → Fil a b y → Fil a b (x + y))
    (hmul : ∀ a b a' b' x y, Fil a b x → Fil a' b' y → Fil (a + a') (b + b') (x * y))
    (hmono : ∀ a b a' b' x, a ≤ a' → b ≤ b' → Fil a b x → Fil a' b' x)
    (hC : ∀ r, Fil 0 0 (φ (C (C r)))) (hX : Fil 1 0 (φ (C X))) (hY : Fil 0 1 (φ X))
    {a b : ℤ} {P : Polynomial (Polynomial F)} (hP : InBox a b P) : Fil a b (φ P) := by
  classical
  have hsum : ∀ {ι : Type _} (s : Finset ι) (g : ι → A) (a b : ℤ),
      (∀ k ∈ s, Fil a b (g k)) → Fil a b (∑ k ∈ s, g k) := by
    intro ι s g a b h
    induction s using Finset.induction_on with
    | empty => simpa using h0 a b
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact hadd _ _ _ _ (h k (Finset.mem_insert_self _ _))
        (ih (fun k' hk' => h k' (Finset.mem_insert_of_mem hk')))
  have hone : Fil 0 0 (1 : A) := by simpa using hC 1
  have hpow : ∀ (x : A) (a b : ℤ) (k : ℕ), Fil a b x → Fil (k * a) (k * b) (x ^ k) := by
    intro x a b k hx
    induction k with
    | zero => simpa using hone
    | succ k ih =>
      rw [pow_succ]
      have := hmul _ _ _ _ _ _ ih hx
      push_cast
      convert this using 1 <;> ring
  rw [P.as_sum_support_C_mul_X_pow, map_sum]
  apply hsum
  intro j hj
  rw [(P.coeff j).as_sum_support_C_mul_X_pow, map_sum, Finset.sum_mul, map_sum]
  apply hsum
  intro i hi
  have hne : (P.coeff j).coeff i ≠ 0 := mem_support_iff.mp hi
  obtain ⟨hia, hjb⟩ := hP j i hne
  simp only [map_mul, map_pow]
  have h1 := hmul _ _ _ _ _ _ (hmul _ _ _ _ _ _ (hC ((P.coeff j).coeff i)) (hpow _ _ _ i hX))
    (hpow _ _ _ j hY)
  refine hmono _ _ _ _ _ ?_ ?_ h1 <;> simp <;> assumption

/-! ### The two-variable box filtration on `F[X][Y][U][V]` -/

/-- The coefficient of `U^e₀ V^e₁` lies in the box `(a - e₀, b - e₁)`. -/
def InBox2 (a b : ℤ) (Ψ : Polynomial (Polynomial (Polynomial (Polynomial F)))) : Prop :=
  ∀ e₁ e₀ : ℕ, InBox (a - e₀) (b - e₁) ((Ψ.coeff e₁).coeff e₀)

theorem inBox2_zero (a b : ℤ) : InBox2 a b (0 : Polynomial (Polynomial (Polynomial
    (Polynomial F)))) := by
  intro e₁ e₀; simpa using inBox_zero _ _

theorem InBox2.add {a b : ℤ} {Ψ Ψ' : Polynomial (Polynomial (Polynomial (Polynomial F)))}
    (h : InBox2 a b Ψ) (h' : InBox2 a b Ψ') : InBox2 a b (Ψ + Ψ') := by
  intro e₁ e₀; simpa using (h e₁ e₀).add (h' e₁ e₀)

theorem InBox2.mono {a b a' b' : ℤ} {Ψ : Polynomial (Polynomial (Polynomial (Polynomial F)))}
    (h : InBox2 a b Ψ) (ha : a ≤ a') (hb : b ≤ b') : InBox2 a' b' Ψ := by
  intro e₁ e₀; exact (h e₁ e₀).mono (by linarith) (by linarith)

theorem InBox2.mul {a b a' b' : ℤ} {Ψ Ψ' : Polynomial (Polynomial (Polynomial (Polynomial F)))}
    (h : InBox2 a b Ψ) (h' : InBox2 a' b' Ψ') : InBox2 (a + a') (b + b') (Ψ * Ψ') := by
  intro e₁ e₀
  rw [coeff_mul, finsetSum_coeff]
  apply inBox_sum
  rintro ⟨j₁, j₂⟩ hj
  rw [coeff_mul]
  apply inBox_sum
  rintro ⟨i₁, i₂⟩ hi
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj hi
  have := (h j₁ i₁).mul (h' j₂ i₂)
  refine this.mono ?_ ?_
  · subst hi; push_cast; linarith
  · subst hj; push_cast; linarith

theorem inBox2_C_C {a b : ℤ} {P : Polynomial (Polynomial F)} (h : InBox a b P) :
    InBox2 a b (C (C P) : Polynomial (Polynomial (Polynomial (Polynomial F)))) := by
  intro e₁ e₀
  rw [coeff_C]
  split_ifs with h1
  · rw [coeff_C]
    split_ifs with h0
    · subst h1 h0; simpa using h
    · exact inBox_zero _ _
  · simpa using inBox_zero _ _

theorem inBox2_X : InBox2 0 1 (X : Polynomial (Polynomial (Polynomial (Polynomial F)))) := by
  intro e₁ e₀
  rw [coeff_X]
  split_ifs with h1
  · rw [coeff_one]
    split_ifs with h0
    · subst h1 h0; simpa using inBox_one
    · exact inBox_zero _ _
  · simpa using inBox_zero _ _

theorem inBox2_C_X : InBox2 1 0 (C X : Polynomial (Polynomial (Polynomial (Polynomial F)))) := by
  intro e₁ e₀
  rw [coeff_C]
  split_ifs with h1
  · rw [coeff_X]
    split_ifs with h0
    · subst h1 h0; simpa using inBox_one
    · exact inBox_zero _ _
  · simpa using inBox_zero _ _

/-! ### The Taylor homomorphism -/

/-- `p(X) ↦ p(X + U)`, valued in `F[X][Y][U]`. -/
def thetaX : Polynomial F →+* Polynomial (Polynomial (Polynomial F)) :=
  Polynomial.eval₂RingHom (R := F) (S := Polynomial (Polynomial (Polynomial F)))
    ((C : Polynomial (Polynomial F) →+* Polynomial (Polynomial (Polynomial F))).comp
      ((C : Polynomial F →+* Polynomial (Polynomial F)).comp C))
    ((C (C (X : Polynomial F)) : Polynomial (Polynomial (Polynomial F))) + X)

/-- The Taylor homomorphism `P(X, Y) ↦ P(X + U, Y + V)`, valued in `F[X][Y][U][V]`. -/
def theta : Polynomial (Polynomial F) →+* Polynomial (Polynomial (Polynomial (Polynomial F))) :=
  Polynomial.eval₂RingHom (R := Polynomial F)
    (S := Polynomial (Polynomial (Polynomial (Polynomial F))))
    ((C : Polynomial (Polynomial (Polynomial F)) →+*
      Polynomial (Polynomial (Polynomial (Polynomial F)))).comp thetaX)
    ((C (C (X : Polynomial (Polynomial F))) : Polynomial (Polynomial (Polynomial
      (Polynomial F)))) + X)

@[simp] theorem theta_C_C (r : F) :
    theta (C (C r) : Polynomial (Polynomial F)) = C (C (C (C r))) := by
  simp [theta, thetaX]

@[simp] theorem theta_C_X :
    theta (C X : Polynomial (Polynomial F)) = C (C (C X) + X) := by
  simp [theta, thetaX]

@[simp] theorem theta_X :
    theta (X : Polynomial (Polynomial F)) = C (C X) + X := by
  simp [theta]

theorem inBox2_theta {a b : ℤ} {P : Polynomial (Polynomial F)} (hP : InBox a b P) :
    InBox2 a b (theta P) := by
  refine map_fil_of_inBox theta InBox2 inBox2_zero (fun a b x y hx hy => hx.add hy)
    (fun a b a' b' x y hx hy => hx.mul hy) (fun a b a' b' x ha hb hx => hx.mono ha hb)
    (fun r => ?_) ?_ ?_ hP
  · rw [theta_C_C]; exact inBox2_C_C (inBox_C_C r)
  · rw [theta_C_X, C_add]
    exact (inBox2_C_C inBox_C_X).add (by simpa using inBox2_C_X)
  · rw [theta_X]
    exact (inBox2_C_C inBox_X).add (by simpa using inBox2_X)

/-- Setting `U = 0` in the Taylor expansion leaves the Taylor expansion in `Y`. -/
theorem theta_map_evalZero (P : Polynomial (Polynomial F)) :
    (theta P).map (evalRingHom 0) = taylor X (P.map C) := by
  have h : (mapRingHom (evalRingHom (0 : Polynomial (Polynomial F)))).comp theta =
      eval₂RingHom ((C : Polynomial (Polynomial F) →+* _).comp C) (X + C X) := by
    apply ringHom_ext'
    · apply ringHom_ext'
      · ext r; simp [theta, thetaX]
      · simp [theta, thetaX]
    · simp [theta, add_comm]
  have := congrArg (fun φ => φ P) h
  simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_eval₂RingHom] at this
  rw [this, taylor_apply, comp, eval₂_map]

theorem theta_coeff_zero (P : Polynomial (Polynomial F)) (k : ℕ) :
    ((theta P).coeff k).coeff 0 = hasseDeriv k P := by
  have h := congrArg (fun p => p.coeff k) (theta_map_evalZero P)
  simp only [coeff_map, coe_evalRingHom, taylor_coeff, hasseDeriv_map] at h
  rw [coeff_zero_eq_eval_zero, h, eval_map, eval₂_C_X]

theorem theta_coeff_zero_zero (P : Polynomial (Polynomial F)) :
    ((theta P).coeff 0).coeff 0 = P := by
  rw [theta_coeff_zero, hasseDeriv_zero, LinearMap.id_apply]

theorem theta_coeff_one_zero (P : Polynomial (Polynomial F)) :
    ((theta P).coeff 1).coeff 0 = derivative P := by
  rw [theta_coeff_zero, hasseDeriv_one]

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
