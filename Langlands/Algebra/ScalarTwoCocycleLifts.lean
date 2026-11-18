import Langlands.Algebra.ScalarTwoCocycleTorsion

/-! # Scalar two-cocycles and normalization of actual lifts -/

noncomputable section
universe u v w

namespace Langlands.ScalarTwoCocycle

variable {Γ : Type u} [Group Γ]
  {A : Type v} [CommGroup A] [MulDistribMulAction Γ A]
  {E : Type w} [Group E] [MulDistribMulAction Γ E]
  (s : A →* E) (hinj : Function.Injective s)
  (hcentral : ∀ (a : A) (x : E), Commute (s a) x)
  (hequiv : ∀ (g : Γ) (a : A), g • s a = s (g • a))

include hinj hcentral hequiv in
/-- Scalar multiplication defects of actual projective lifts satisfy the scalar
two-cocycle identity. -/
theorem isTwoCocycle_of_lifts (x : Γ → E) (c : Γ → Γ → A)
    (hlift : ∀ g h, x g * (g • x h) = s (c g h) * x (g * h)) :
    IsTwoCocycle c := by
  intro g h t
  apply hinj
  apply mul_right_cancel (b := x (g * (h * t)))
  simp only [map_mul]
  calc
    (s (c g h) * s (c (g * h) t)) * x (g * (h * t)) =
        s (c g h) * (x (g * h) * ((g * h) • x t)) := by
      rw [← mul_assoc g h t, mul_assoc, ← hlift (g * h) t]
    _ = (x g * (g • x h)) * ((g * h) • x t) := by
      rw [← mul_assoc, ← hlift g h]
    _ = x g * (g • (x h * (h • x t))) := by
      rw [smul_mul', mul_smul]
      exact mul_assoc _ _ _
    _ = x g * (g • (s (c h t) * x (h * t))) := by rw [hlift h t]
    _ = s (g • c h t) * (x g * (g • x (h * t))) := by
      rw [smul_mul', hequiv, ← mul_assoc, (hcentral _ _).symm.eq, mul_assoc]
    _ = (s (g • c h t) * s (c g (h * t))) * x (g * (h * t)) := by
      rw [hlift g (h * t), mul_assoc]

include hcentral hequiv in
/-- Rescaling actual projective lifts by a trivializing scalar cochain gives an
honest multiplicative one-cocycle. -/
theorem normalized_lifts_mul (x : Γ → E) (c : Γ → Γ → A)
    (hlift : ∀ g h, x g * (g • x h) = s (c g h) * x (g * h))
    (b : Γ → A) (hb : ∀ g h, c g h = coboundary b g h) (g h : Γ) :
    (s (b g))⁻¹ * x g * (g • ((s (b h))⁻¹ * x h)) =
      (s (b (g * h)))⁻¹ * x (g * h) := by
  rw [smul_mul', smul_inv', hequiv]
  calc
    (s (b g))⁻¹ * x g * ((s (g • b h))⁻¹ * (g • x h)) =
        (s (b g))⁻¹ * (s (g • b h))⁻¹ * (x g * (g • x h)) := by
      rw [← mul_assoc, mul_assoc (s (b g))⁻¹, (hcentral _ _).symm.inv_right.eq]
      group
    _ = (s (b g))⁻¹ * (s (g • b h))⁻¹ * (s (c g h) * x (g * h)) := by rw [hlift]
    _ = (s (b (g * h)))⁻¹ * x (g * h) := by
      rw [hb, coboundary, map_mul, map_mul, map_inv]
      have hc := hcentral (b g) (s (g • b h))
      rw [hc.inv_left.inv_right.eq]
      group

include hcentral hequiv in
/-- A projective lift whose scalar defect is an actual coboundary can be
rescaled into an honest one-cocycle. -/
theorem exists_honest_lifts_of_isCoboundary (x : Γ → E) (c : Γ → Γ → A)
    (hlift : ∀ g h, x g * (g • x h) = s (c g h) * x (g * h))
    (hc : IsCoboundary c) :
    ∃ b : Γ → A, ∀ g h,
      (s (b g))⁻¹ * x g * (g • ((s (b h))⁻¹ * x h)) =
        (s (b (g * h)))⁻¹ * x (g * h) := by
  obtain ⟨b, hb⟩ := hc
  exact ⟨b, normalized_lifts_mul s hcentral hequiv x c hlift b hb⟩

end Langlands.ScalarTwoCocycle
