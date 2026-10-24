import Langlands.Shimura.Unitary.Reflex

noncomputable section
open NumberField Algebra
open scoped Classical

namespace Langlands.Shimura

universe u v

/-- The Galois permutation of complex embeddings is postcomposition. -/
def complexEmbeddingGaloisAction (K : Type v) [Semiring K] :
    (ℂ ≃ₐ[ℚ] ℂ) →* Equiv.Perm (K →+* ℂ) where
  toFun s :=
    { toFun := fun i => (s : ℂ →+* ℂ).comp i
      invFun := fun i => (s.symm : ℂ →+* ℂ).comp i
      left_inv := fun i => RingHom.ext fun x => s.symm_apply_apply (i x)
      right_inv := fun i => RingHom.ext fun x => s.apply_symm_apply (i x) }
  map_one' := by ext i x; rfl
  map_mul' s t := by ext i x; rfl

@[simp] theorem complexEmbeddingGaloisAction_apply (K : Type v) [Semiring K]
    (s : ℂ ≃ₐ[ℚ] ℂ) (i : K →+* ℂ) :
    complexEmbeddingGaloisAction K s i = (s : ℂ →+* ℂ).comp i := rfl

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  (Φ : (E →+* ℝ) → (K →+* ℂ)) (hΦ : IsCMSection E K Φ)

/-- The selected CM embedding is the first factor; its conjugate is the second. -/
def cmFactorEmbedding (p : (E →+* ℝ) × Bool) : K →+* ℂ :=
  if p.2 then Φ p.1 else ComplexEmbedding.conjugate (Φ p.1)

include hΦ in
omit [NumberField E] [NumberField K] [IsTotallyComplex K]
  [IsQuadraticExtension E K] in
theorem realPlaceBelow_cmFactorEmbedding (p : (E →+* ℝ) × Bool) :
    realPlaceBelow E (cmFactorEmbedding Φ p) = p.1 := by
  rcases p with ⟨τ, b⟩
  cases b <;> simp [cmFactorEmbedding, realPlaceBelow_conjugate,
    realPlaceBelow_of_isCMSection E hΦ]

omit [NumberField E] [IsTotallyReal E] [NumberField K] [Algebra E K]
  [IsQuadraticExtension E K] in
private theorem conjugate_section_ne (τ : E →+* ℝ) :
    ComplexEmbedding.conjugate (Φ τ) ≠ Φ τ :=
  fun h => IsTotallyComplex.complexEmbedding_not_isReal (Φ τ)
    (ComplexEmbedding.isReal_iff.mpr h)

/-- Every complex embedding is exactly one of the two factors over its real place. -/
def cmFactorEmbeddingEquiv (hΦ : IsCMSection E K Φ) : ((E →+* ℝ) × Bool) ≃ (K →+* ℂ) where
  toFun := cmFactorEmbedding Φ
  invFun i := ⟨realPlaceBelow E i, decide (i = Φ (realPlaceBelow E i))⟩
  left_inv := by
    rintro ⟨τ, b⟩
    cases b <;>
      simp [cmFactorEmbedding, realPlaceBelow_conjugate,
        realPlaceBelow_of_isCMSection E hΦ, conjugate_section_ne Φ]
  right_inv := by
    intro i
    change (if decide (i = Φ (realPlaceBelow E i)) then
      Φ (realPlaceBelow E i) else
      ComplexEmbedding.conjugate (Φ (realPlaceBelow E i))) = i
    by_cases h : i = Φ (realPlaceBelow E i)
    · rw [ite_eq_left (by simpa using h)]
      exact h.symm
    · have hc : i.comp (algebraMap E K) =
          (Φ (realPlaceBelow E i)).comp (algebraMap E K) :=
        (comp_realPlaceBelow E i).trans (hΦ _).symm
      have hi := (eq_or_eq_conjugate_of_comp_eq (Φ (realPlaceBelow E i)) i hc).resolve_left h
      rw [ite_eq_right (by simpa using h)]
      exact hi.symm

@[simp] theorem cmFactorEmbeddingEquiv_apply (p : (E →+* ℝ) × Bool) :
    cmFactorEmbeddingEquiv Φ hΦ p = cmFactorEmbedding Φ p := rfl

@[simp] theorem cmFactorEmbeddingEquiv_symm_fst (i : K →+* ℂ) :
    ((cmFactorEmbeddingEquiv Φ hΦ).symm i).1 = realPlaceBelow E i := rfl

theorem cmFactorEmbeddingEquiv_symm_snd (i : K →+* ℂ) :
    ((cmFactorEmbeddingEquiv Φ hΦ).symm i).2 = true ↔
      i = Φ (realPlaceBelow E i) := by
  change decide (i = Φ (realPlaceBelow E i)) = true ↔ _
  exact decide_eq_true_iff

/-- The Galois action transported to the real-place/Boolean factor indices. -/
def cmFactorGaloisAction (hΦ : IsCMSection E K Φ) :
    (ℂ ≃ₐ[ℚ] ℂ) →* Equiv.Perm ((E →+* ℝ) × Bool) where
  toFun s := (cmFactorEmbeddingEquiv Φ hΦ).trans
    ((complexEmbeddingGaloisAction K s).trans (cmFactorEmbeddingEquiv Φ hΦ).symm)
  map_one' := by
    apply Equiv.ext
    intro p
    simp only [Equiv.trans_apply, map_one, Equiv.Perm.one_apply,
      Equiv.symm_apply_apply]
  map_mul' s t := by
    apply Equiv.ext
    intro p
    simp only [Equiv.trans_apply, map_mul, Equiv.Perm.mul_apply,
      Equiv.apply_symm_apply]

/-- Under the embedding equivalence the index action is postcomposition by `s`. -/
@[simp] theorem cmFactorEmbeddingEquiv_galois (s : ℂ ≃ₐ[ℚ] ℂ)
    (p : (E →+* ℝ) × Bool) :
    cmFactorEmbeddingEquiv Φ hΦ (cmFactorGaloisAction Φ hΦ s p) =
      (s : ℂ →+* ℂ).comp (cmFactorEmbedding Φ p) := by
  exact (cmFactorEmbeddingEquiv Φ hΦ).apply_symm_apply _

theorem cmFactorGaloisAction_fst (s : ℂ ≃ₐ[ℚ] ℂ) (p : (E →+* ℝ) × Bool) :
    (cmFactorGaloisAction Φ hΦ s p).1 =
      realPlaceBelow E ((s : ℂ →+* ℂ).comp (cmFactorEmbedding Φ p)) := rfl

theorem cmFactorGaloisAction_snd (s : ℂ ≃ₐ[ℚ] ℂ) (p : (E →+* ℝ) × Bool) :
    (cmFactorGaloisAction Φ hΦ s p).2 = true ↔
      (s : ℂ →+* ℂ).comp (cmFactorEmbedding Φ p) =
        Φ (realPlaceBelow E ((s : ℂ →+* ℂ).comp (cmFactorEmbedding Φ p))) := by
  exact cmFactorEmbeddingEquiv_symm_snd Φ hΦ _

/-- The existing Hodge stabilizer can be tested on the explicit CM factor indices. -/
theorem mem_hodgeStabilizer_cmFactor (f : (K →+* ℂ) → ℕ) (s : ℂ ≃ₐ[ℚ] ℂ) :
    s ∈ hodgeStabilizer f ↔ ∀ p : (E →+* ℝ) × Bool,
      f (cmFactorEmbedding Φ (cmFactorGaloisAction Φ hΦ s p)) =
        f (cmFactorEmbedding Φ p) := by
  constructor
  · intro h p
    change f (cmFactorEmbeddingEquiv Φ hΦ (cmFactorGaloisAction Φ hΦ s p)) = _
    rw [cmFactorEmbeddingEquiv_galois]
    exact h _
  · intro h i
    obtain ⟨p, rfl⟩ := (cmFactorEmbeddingEquiv Φ hΦ).surjective i
    have hp := h p
    change f (cmFactorEmbeddingEquiv Φ hΦ (cmFactorGaloisAction Φ hΦ s p)) = _ at hp
    rw [cmFactorEmbeddingEquiv_galois] at hp
    exact hp

end Langlands.Shimura
