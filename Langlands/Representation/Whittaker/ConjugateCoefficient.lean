import Langlands.Representation.Whittaker.Algebraic
import Langlands.Representation.Unitary.HermitianDual

/-! # Conjugate Whittaker functionals and positive coefficient products -/

noncomputable section

namespace Langlands.Whittaker

universe uG uV uW

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (N : Subgroup G) (θ : N →* ℂˣ)
  {π : Representation ℂ G V} {σ : Representation ℂ G W}
  (E : V ≃ₗ⋆[ℂ] W)
  (hE : ∀ g v, E (π g v) = σ g (E v))
  (hθ : ∀ n : N, ‖(θ n : ℂ)‖ = 1)

/-- Conjugating a functional after an equivariant conjugate-linear equivalence
produces a linear functional with the inverse unitary character. -/
def conjugateFunctional (ℓ : functionals N θ π) :
    functionals N θ⁻¹ σ :=
  ⟨{ toFun := fun w => starRingEnd ℂ (ℓ.val (E.symm w))
     map_add' := by
       intro w w'
       simp only [map_add]
     map_smul' := by
       intro c w
       rw [E.symm.map_smulₛₗ, ℓ.val.map_smul]
       simp [smul_eq_mul] },
    by
      intro n w
      have hinv : E.symm (σ n.val w) = π n.val (E.symm w) := by
        apply E.injective
        rw [E.apply_symm_apply, hE, E.apply_symm_apply]
      change starRingEnd ℂ (ℓ.val (E.symm (σ n.val w))) =
        (θ⁻¹ n : ℂ) * starRingEnd ℂ (ℓ.val (E.symm w))
      rw [hinv, ℓ.property, map_mul]
      simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      rw [Complex.inv_eq_conj (hθ n)]⟩

@[simp]
theorem conjugateFunctional_apply (ℓ : functionals N θ π) (w : W) :
    (conjugateFunctional N θ E hE hθ ℓ).val w =
      starRingEnd ℂ (ℓ.val (E.symm w)) := rfl

@[simp]
theorem conjugateFunctional_apply_equiv (ℓ : functionals N θ π) (v : V) :
    (conjugateFunctional N θ E hE hθ ℓ).val (E v) =
      starRingEnd ℂ (ℓ.val v) := by
  rw [conjugateFunctional_apply, E.symm_apply_apply]

/-- The transport preserves a nonzero functional. -/
theorem conjugateFunctional_nonzero
    (ℓ : functionals N θ π) (hℓ : ℓ.val ≠ 0) :
    (conjugateFunctional N θ E hE hθ ℓ).val ≠ 0 := by
  intro hzero
  apply hℓ
  ext v
  have hv : starRingEnd ℂ (ℓ.val v) = 0 := by
    simpa only [conjugateFunctional_apply_equiv, LinearMap.zero_apply] using
      LinearMap.congr_fun hzero (E v)
  exact (starRingEnd ℂ).injective (hv.trans (map_zero _).symm)

/-- The transported coefficient at `E v` is the complex conjugate of the
original coefficient at every group element. -/
theorem coefficient_conjugateFunctional
    (ℓ : functionals N θ π) (v : V) (g : G) :
    (coefficientMap σ (conjugateFunctional N θ E hE hθ ℓ) (E v)).val g =
      starRingEnd ℂ ((coefficientMap π ℓ v).val g) := by
  change starRingEnd ℂ (ℓ.val (E.symm (σ g (E v)))) =
    starRingEnd ℂ (ℓ.val (π g v))
  rw [← hE, E.symm_apply_apply]

/-- The product is the actual squared norm, with its usual real value embedded
in the complex numbers. -/
theorem coefficient_mul_conjugateFunctional
    (ℓ : functionals N θ π) (v : V) (g : G) :
    (coefficientMap π ℓ v).val g *
        (coefficientMap σ (conjugateFunctional N θ E hE hθ ℓ) (E v)).val g =
      ((‖(coefficientMap π ℓ v).val g‖ ^ 2 : ℝ) : ℂ) := by
  rw [coefficient_conjugateFunctional]
  exact (Complex.mul_conj' _).trans (Complex.ofReal_pow _ _).symm

/-- A nonzero functional gives a pair whose product is strictly positive at
the identity. This is a pointwise assertion, without an integration claim. -/
theorem exists_coefficient_product_pos
    (ℓ : functionals N θ π) (hℓ : ℓ.val ≠ 0) :
    ∃ v : V, 0 <
      ((coefficientMap π ℓ v).val 1 *
        (coefficientMap σ (conjugateFunctional N θ E hE hθ ℓ) (E v)).val 1).re := by
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ.val v ≠ 0 := by
    by_contra h
    apply hℓ
    ext v
    exact not_not.mp (not_exists.mp h v)
  refine ⟨v, ?_⟩
  rw [coefficient_mul_conjugateFunctional]
  change 0 < ‖ℓ.val (π 1 v)‖ ^ 2
  simpa only [map_one, Module.End.one_apply] using
    sq_pos_of_pos (norm_pos_iff.mpr hv)

section HermitianDual

variable [TopologicalSpace G] [IsTopologicalGroup G]
  (b : InvariantPositiveForm π)
  (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hπ : IsAdmissible π)

/-- An invariant positive form transports a Whittaker functional to the actual
smooth contragredient, with the inverse unitary character. -/
def hermitianDualFunctional (ℓ : functionals N θ π) :
    functionals N θ⁻¹ (smoothContragredient π) :=
  conjugateFunctional N θ (b.smoothDualEquiv hcofinal hπ)
    (b.toSmoothDual_apply_action hπ.1) hθ ℓ

/-- The functional on the smooth contragredient is nonzero. -/
theorem hermitianDualFunctional_nonzero
    (ℓ : functionals N θ π) (hℓ : ℓ.val ≠ 0) :
    (hermitianDualFunctional N θ hθ b hcofinal hπ ℓ).val ≠ 0 :=
  conjugateFunctional_nonzero N θ (b.smoothDualEquiv hcofinal hπ)
    (b.toSmoothDual_apply_action hπ.1) hθ ℓ hℓ

/-- The actual smooth-dual coefficient is the conjugate coefficient. -/
theorem coefficient_hermitianDualFunctional
    (ℓ : functionals N θ π) (v : V) (g : G) :
    (coefficientMap (smoothContragredient π)
      (hermitianDualFunctional N θ hθ b hcofinal hπ ℓ)
      (b.toSmoothDual hπ.1 v)).val g =
        starRingEnd ℂ ((coefficientMap π ℓ v).val g) :=
  coefficient_conjugateFunctional N θ (b.smoothDualEquiv hcofinal hπ)
    (b.toSmoothDual_apply_action hπ.1) hθ ℓ v g

/-- The coefficient pair from a positive form has squared-norm product. -/
theorem coefficient_mul_hermitianDualFunctional
    (ℓ : functionals N θ π) (v : V) (g : G) :
    (coefficientMap π ℓ v).val g *
      (coefficientMap (smoothContragredient π)
        (hermitianDualFunctional N θ hθ b hcofinal hπ ℓ)
        (b.toSmoothDual hπ.1 v)).val g =
      ((‖(coefficientMap π ℓ v).val g‖ ^ 2 : ℝ) : ℂ) :=
  coefficient_mul_conjugateFunctional N θ (b.smoothDualEquiv hcofinal hπ)
    (b.toSmoothDual_apply_action hπ.1) hθ ℓ v g

end HermitianDual

end Langlands.Whittaker
