import Langlands.Representation.Unitary.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Extending similarities between positive-form completions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.InvariantPositiveForm

universe uG uV uW

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The exact norm ratio on the canonical dense embeddings. -/
theorem norm_toHilbert_of_inner (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w) (v : V) :
    ‖c.toHilbert (e v)‖ = Real.sqrt a * ‖b.toHilbert v‖ := by
  calc
    ‖c.toHilbert (e v)‖ = Real.sqrt (c.inner (e v) (e v)).re :=
      c.norm_toHilbert (e v)
    _ = Real.sqrt (((a : ℂ) * b.inner v v).re) :=
      congrArg (fun z : ℂ => Real.sqrt z.re) (hinner v v)
    _ = Real.sqrt a * Real.sqrt (b.inner v v).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact Real.sqrt_mul ha.le _
    _ = Real.sqrt a * ‖b.toHilbert v‖ :=
      congrArg (Real.sqrt a * ·) (b.norm_toHilbert v).symm

/-- The inverse has the reciprocal norm ratio. -/
theorem norm_toHilbert_symm_of_inner (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w) (w : W) :
    ‖b.toHilbert (e.symm w)‖ = (Real.sqrt a)⁻¹ * ‖c.toHilbert w‖ := by
  have h : ‖c.toHilbert w‖ = Real.sqrt a * ‖b.toHilbert (e.symm w)‖ :=
    (congrArg (fun z : W => ‖c.toHilbert z‖) (e.apply_symm_apply w)).symm.trans
      (b.norm_toHilbert_of_inner c e a ha hinner (e.symm w))
  exact (eq_inv_mul_iff_mul_eq₀ (ne_of_gt (Real.sqrt_pos.mpr ha))).mpr h.symm

/-- Extend the original equivalence between the two independently supplied
form completions, retaining its positive inner-product ratio. -/
def hilbertEquivalenceOfInner (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w) :
    b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion :=
  e.extend b.toHilbert c.toHilbert b.denseRange_toHilbert
    ⟨Real.sqrt a, fun v => (b.norm_toHilbert_of_inner c e a ha hinner v).le⟩
    c.denseRange_toHilbert
    ⟨(Real.sqrt a)⁻¹, fun w => (b.norm_toHilbert_symm_of_inner c e a ha hinner w).le⟩

@[simp]
theorem hilbertEquivalenceOfInner_toHilbert (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w) (v : V) :
    b.hilbertEquivalenceOfInner c e a ha hinner (b.toHilbert v) = c.toHilbert (e v) :=
  LinearEquiv.extend_eq _ _ _ _ _ _ _ _

@[simp]
theorem hilbertEquivalenceOfInner_symm_toHilbert (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w) (w : W) :
    (b.hilbertEquivalenceOfInner c e a ha hinner).symm (c.toHilbert w) =
      b.toHilbert (e.symm w) :=
  LinearEquiv.extend_symm_eq _ _ _ _ _ _ _ _

/-- The dense embeddings determine any continuous extension uniquely. -/
theorem hilbertEquivalence_unique (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W)
    (E E' : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion)
    (hE : ∀ v, E (b.toHilbert v) = c.toHilbert (e v))
    (hE' : ∀ v, E' (b.toHilbert v) = c.toHilbert (e v)) : E = E' := by
  ext x
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq E.continuous E'.continuous
  · intro v
    exact (hE v).trans (hE' v).symm

/-- Covariance extends for any pair of operators with prescribed continuous
extensions on the two actual completions. -/
theorem hilbertEquivalence_covariant (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W)
    (E : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion)
    (hE : ∀ v, E (b.toHilbert v) = c.toHilbert (e v))
    (A : Module.End ℂ V) (D : Module.End ℂ W)
    (Ac : b.HilbertCompletion →L[ℂ] b.HilbertCompletion)
    (Dc : c.HilbertCompletion →L[ℂ] c.HilbertCompletion)
    (hA : ∀ v, Ac (b.toHilbert v) = b.toHilbert (A v))
    (hD : ∀ w, Dc (c.toHilbert w) = c.toHilbert (D w))
    (he : ∀ v, e (A v) = D (e v)) (x : b.HilbertCompletion) :
    E (Ac x) = Dc (E x) := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq (E.continuous.comp Ac.continuous) (Dc.continuous.comp E.continuous)
  · intro v
    exact (congrArg E (hA v)).trans
      ((hE (A v)).trans ((congrArg c.toHilbert (he v)).trans
        ((hD (e v)).symm.trans (congrArg Dc (hE v)).symm)))

/-- The inner-product ratio extends by density in each variable. -/
theorem hilbertEquivalence_inner (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W)
    (E : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion)
    (hE : ∀ v, E (b.toHilbert v) = c.toHilbert (e v))
    (a : ℝ) (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w)
    (x y : b.HilbertCompletion) :
    Inner.inner ℂ (E x) (E y) = (a : ℂ) * Inner.inner ℂ x y := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq (E.continuous.inner continuous_const)
      (continuous_const.mul (continuous_id.inner continuous_const))
  · intro v
    refine b.denseRange_toHilbert.induction_on y ?_ ?_
    · exact isClosed_eq (continuous_const.inner E.continuous)
        (continuous_const.mul (continuous_const.inner continuous_id))
    · intro w
      exact (congrArg₂ (Inner.inner ℂ) (hE v) (hE w)).trans
        ((c.inner_toHilbert (e v) (e w)).trans
          ((hinner v w).trans
            (congrArg ((a : ℂ) * ·) (b.inner_toHilbert v w)).symm))

/-- A similarity of the algebraic forms has a continuous extension with the same
inner-product ratio on the entire prescribed completions. -/
theorem exists_hilbertEquivalence_of_inner (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (e : V ≃ₗ[ℂ] W) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w) :
    ∃ E : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion,
      (∀ v, E (b.toHilbert v) = c.toHilbert (e v)) ∧
      (∀ x y, Inner.inner ℂ (E x) (E y) = (a : ℂ) * Inner.inner ℂ x y) := by
  let E := b.hilbertEquivalenceOfInner c e a ha hinner
  have hE : ∀ v, E (b.toHilbert v) = c.toHilbert (e v) :=
    b.hilbertEquivalenceOfInner_toHilbert c e a ha hinner
  exact ⟨E, hE, b.hilbertEquivalence_inner c e E hE a hinner⟩

end Langlands.InvariantPositiveForm
