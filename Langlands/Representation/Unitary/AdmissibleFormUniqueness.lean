import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Unitary.PositiveFormTensor
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Positive-form uniqueness for irreducible admissible representations

Comparing the two actual Hermitian identifications gives a linear intertwiner.
Admissible Schur and a nonzero diagonal pairing make its scalar positive real.
-/

noncomputable section

open scoped ComplexConjugate

namespace Langlands.InvariantPositiveForm

universe uG uV

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- A diagonal pairing is the complex embedding of its real part. -/
theorem inner_self_ofReal_re (b : InvariantPositiveForm ρ) (v : V) :
    ((b.inner v v).re : ℂ) = b.inner v v := by
  let := b.toInnerProductCore
  exact InnerProductSpace.Core.inner_self_ofReal_re v

/-- A nonzero vector has strictly positive real diagonal pairing. -/
theorem inner_self_re_pos (b : InvariantPositiveForm ρ) {v : V} (hv : v ≠ 0) :
    0 < (b.inner v v).re := by
  let := b.toInnerProductCore
  exact lt_of_le_of_ne (b.re_inner_nonneg v)
    (fun hz => hv ((InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hz.symm))

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The linear equivariant comparison `E_b⁻¹ ∘ E_c` of the actual
conjugate-linear Hermitian identifications. -/
def comparisonIntertwiner (b c : InvariantPositiveForm ρ)
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsAdmissible ρ) :
    ρ.IntertwiningMap ρ := by
  let e : V ≃ₗ[ℂ] V := (c.smoothDualEquiv hcof hρ).trans
    (b.smoothDualEquiv hcof hρ).symm
  refine e.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ ?_
  intro g v
  apply (b.smoothDualEquiv hcof hρ).injective
  change b.smoothDualEquiv hcof hρ
      ((b.smoothDualEquiv hcof hρ).symm (c.smoothDualEquiv hcof hρ (ρ g v))) =
    b.smoothDualEquiv hcof hρ
      (ρ g ((b.smoothDualEquiv hcof hρ).symm (c.smoothDualEquiv hcof hρ v)))
  rw [LinearEquiv.apply_symm_apply]
  change c.toSmoothDual hρ.1 (ρ g v) =
    b.toSmoothDual hρ.1
      (ρ g ((b.smoothDualEquiv hcof hρ).symm (c.smoothDualEquiv hcof hρ v)))
  rw [c.toSmoothDual_apply_action, b.toSmoothDual_apply_action]
  exact congrArg (smoothContragredient ρ g)
    ((b.smoothDualEquiv hcof hρ).apply_symm_apply _).symm

/-- Applying the comparison in the first argument turns the first form into
the second form. -/
theorem comparisonIntertwiner_inner (b c : InvariantPositiveForm ρ)
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsAdmissible ρ) (v w : V) :
    b.inner (b.comparisonIntertwiner c hcof hρ v) w = c.inner v w := by
  have he := (b.smoothDualEquiv hcof hρ).apply_symm_apply
    (c.smoothDualEquiv hcof hρ v)
  exact congrArg (fun ℓ : SmoothDual ρ => ℓ.val w) he

/-- Two invariant positive forms on an irreducible admissible complex
representation differ by a strictly positive real scalar. -/
theorem exists_pos_rescale_eq (b c : InvariantPositiveForm ρ)
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsAdmissible ρ)
    (hi : ρ.IsIrreducible) :
    ∃ a : ℝ, ∃ ha : 0 < a, c = b.rescale a ha := by
  obtain ⟨z, hz, _⟩ := admissibleSchur_scalarEndomorphism ρ hρ hi
    (b.comparisonIntertwiner c hcof hρ)
  have hinner (v w : V) : c.inner v w = conj z * b.inner v w := by
    rw [← b.comparisonIntertwiner_inner c hcof hρ v w]
    have hv : b.comparisonIntertwiner c hcof hρ v = z • v :=
      congrArg (fun T : ρ.IntertwiningMap ρ => T v) hz
    rw [hv, b.smul_left]
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let a : ℝ := (c.inner v v).re / (b.inner v v).re
  have ha : 0 < a := div_pos (c.inner_self_re_pos hv) (b.inner_self_re_pos hv)
  have hzreal : conj z = (a : ℂ) := by
    apply mul_right_cancel₀ (show b.inner v v ≠ 0 from fun he => hv (b.definite v he))
    calc
      conj z * b.inner v v = c.inner v v := (hinner v v).symm
      _ = ((c.inner v v).re : ℂ) := (c.inner_self_ofReal_re v).symm
      _ = (a : ℂ) * b.inner v v := by
        rw [← b.inner_self_ofReal_re v, ← Complex.ofReal_mul]
        exact congrArg (fun r : ℝ => (r : ℂ))
          (div_mul_cancel₀ (c.inner v v).re (b.inner_self_re_pos hv).ne').symm
  refine ⟨a, ha, ?_⟩
  apply ext_inner
  intro x y
  rw [rescale_inner, hinner, hzreal]

end Langlands.InvariantPositiveForm
