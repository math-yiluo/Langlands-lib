import Langlands.BaseChange.Norm

/-!
# Cyclic norms of polynomial perturbations

For the norm neighbourhood argument, an `l`-th power is a norm, and a norm
remains a norm after multiplication by the `l`-th power of an invertible
polynomial in its matrix and subsequent conjugation.
-/

namespace Langlands.BaseChange

universe u v

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]

/-- An `l`-th power is the norm of the base change of its root. -/
theorem isNorm_pow (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (s : GeneralLinear n F) :
    IsNorm σ l (s ^ l) := by
  have hone : cyclicNorm σ l (1 : GeneralLinear n E) = 1 := by
    induction l with
    | zero => rfl
    | succ l ih => rw [cyclicNorm_succ, ih, map_one, one_mul]
  refine ⟨baseChange F E n s, 1, ?_⟩
  simpa only [one_mul, inv_one, mul_one, hone, map_pow] using
    cyclicNorm_mul_baseChange σ l 1 s (Commute.one_left _)

/-- Conjugates of `γ * s ^ l` are norms when `γ` is a norm and the matrix of `s` is
`1` plus the indicated polynomial in the matrix of `γ`. -/
theorem IsNorm.conj_mul_pow_of_polynomial {σ : E ≃ₐ[F] E} {l n : ℕ} {γ : GeneralLinear n F}
    (h : IsNorm σ l γ) (hσ : σ ^ l = 1) (g s : GeneralLinear n F) (c : Fin n → F)
    (hs : s.val = 1 + ∑ i : Fin n, c i • γ.val ^ (i : ℕ)) :
    IsNorm σ l (g * γ * s ^ l * g⁻¹) := by
  obtain ⟨δ₀, x, hx⟩ := h
  let δ := x⁻¹ * δ₀ * entrywiseAut σ n x
  have hδ : cyclicNorm σ l δ = baseChange F E n γ := by
    dsimp only [δ]
    rw [cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, hx]
  have hcomm : Commute δ (baseChange F E n γ) := by
    have hfixed := entrywiseAut_cyclicNorm σ l δ
    rw [hσ, entrywiseAut_one_apply, hδ, entrywiseAut_baseChange] at hfixed
    calc
      δ * baseChange F E n γ = δ * (δ⁻¹ * baseChange F E n γ * δ) :=
        congrArg (δ * ·) hfixed
      _ = baseChange F E n γ * δ := by group
  let φ : Matrix (Fin n) (Fin n) F →ₐ[F] Matrix (Fin n) (Fin n) E :=
    (Algebra.ofId F E).mapMatrix
  have hφγ : Commute δ.val (φ γ.val) := hcomm.map (Units.coeHom _)
  have hcomms : Commute δ (baseChange F E n s) := by
    change δ * baseChange F E n s = baseChange F E n s * δ
    apply Units.ext
    change Commute δ.val (φ s.val)
    rw [hs, map_add, map_one, map_sum]
    refine (Commute.one_right _).add_right (Commute.sum_right _ _ _ ?_)
    intro i _
    rw [map_smul, map_pow]
    exact (hφγ.pow_right (i : ℕ)).smul_right (c i)
  have hnorm : IsNormAssociated σ l (δ * baseChange F E n s) (γ * s ^ l) := by
    refine ⟨1, ?_⟩
    rw [inv_one, one_mul, mul_one, cyclicNorm_mul_baseChange σ l δ s hcomms, hδ, map_mul,
      map_pow]
  refine ⟨δ * baseChange F E n s, ?_⟩
  simpa only [inv_inv, inv_one, one_mul, map_one, mul_one, mul_assoc] using
    hnorm.twistedConj hσ 1 g⁻¹

end Langlands.BaseChange
