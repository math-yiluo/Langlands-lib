import Langlands.Representation.Whittaker.ConjugateCoefficient
import Langlands.Representation.Whittaker.AlgebraicTwist
import Langlands.Representation.Whittaker.Transport
import Langlands.Representation.Smooth.Contragredient.Equivalence
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Representation.Twist.AlgebraProof

/-! # Squared-norm coefficient products for a twisted contragredient pair -/

noncomputable section

namespace Langlands.Whittaker

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}
  (χ α : G →* ℂˣ)
  (hχ : IsOpen (χ.ker : Set G)) (hα : IsOpen (α.ker : Set G))
  (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hσ : IsAdmissible σ)
  (e : (Langlands.twist χ π).Equiv (smoothContragredient σ))

/-- Dualize a twisted contragredient equivalence and compare with the smooth
dual of any further open-kernel twist. -/
def twistedDualTransportEquiv :
    σ.Equiv (Langlands.twist (χ⁻¹ * α)
      (smoothContragredient (Langlands.twist α π))) := by
  let bidual : σ.Equiv (smoothContragredient (smoothContragredient σ)) :=
    (smoothBidual hσ.1).ofBijective
      ⟨smoothBidual_injective_of_compact_cofinal hcofinal σ hσ.1,
        smoothBidual_surjective_of_compact_cofinal hcofinal σ hσ⟩
  let d : σ.Equiv (Langlands.twist χ⁻¹ (smoothContragredient π)) :=
    (bidual.trans (smoothContragredientEquiv e)).trans
      (smoothContragredientTwistEquiv χ π hχ)
  have a : (Langlands.twist α
      (smoothContragredient (Langlands.twist α π))).Equiv
        (smoothContragredient π) := by
    simpa only [twist_twist_inv] using
      twistEquiv α (smoothContragredientTwistEquiv α π hα)
  simpa only [twist_twist] using d.trans (twistEquiv χ⁻¹ a.symm)

include hχ hα hcofinal hσ e in
/-- For a twisted contragredient pair, a positive form on a further twist of
the first member produces actual inverse-character coefficients on the second
member. Their product is the inverse original character times a squared norm. -/
theorem exists_twisted_conjugate_functional
    (N : Subgroup G) (θ : N →* ℂˣ)
    (hχN : ∀ n : N, χ n.val = 1) (hαN : ∀ n : N, α n.val = 1)
    (hθ : ∀ n : N, ‖(θ n : ℂ)‖ = 1)
    (hτ : IsAdmissible (Langlands.twist α π))
    (b : InvariantPositiveForm (Langlands.twist α π))
    (ℓ : functionals N θ π) (hℓ : ℓ.val ≠ 0) :
    ∃ m : functionals N θ⁻¹ σ, m.val ≠ 0 ∧
      ∀ v : V, ∃ w : W, ∀ g : G,
        (coefficientMap π ℓ v).val g * (coefficientMap σ m w).val g =
          (χ g : ℂ)⁻¹ *
            ((‖(coefficientMap (Langlands.twist α π)
              (twistFunctional N θ α hαN π ℓ) v).val g‖ ^ 2 : ℝ) : ℂ) := by
  let τ := Langlands.twist α π
  let δ := χ⁻¹ * α
  have hδN : ∀ n : N, δ n.val = 1 := by
    intro n
    simp [δ, hχN n, hαN n]
  let d := twistedDualTransportEquiv χ α hχ hα hcofinal hσ e
  let ℓτ := twistFunctional N θ α hαN π ℓ
  let m₀ := hermitianDualFunctional N θ hθ b hcofinal hτ ℓτ
  let m₁ := twistFunctional N θ⁻¹ δ hδN (smoothContragredient τ) m₀
  let m := functionalsComap d.toIntertwiningMap m₁
  have hm₀ : m₀.val ≠ 0 :=
    hermitianDualFunctional_nonzero N θ hθ b hcofinal hτ ℓτ hℓ
  refine ⟨m, ?_, fun v => ⟨d.symm (b.toSmoothDual hτ.1 v), fun g => ?_⟩⟩
  · intro hm
    apply hm₀
    ext ξ
    obtain ⟨w, rfl⟩ := d.toLinearEquiv.surjective ξ
    exact LinearMap.congr_fun hm w
  · have hsecond :
        (coefficientMap σ m (d.symm (b.toSmoothDual hτ.1 v))).val g =
          (δ g : ℂ) * starRingEnd ℂ ((coefficientMap τ ℓτ v).val g) := by
      change m₀.val (d (σ g (d.symm (b.toSmoothDual hτ.1 v)))) = _
      erw [d.isIntertwining, d.apply_symm_apply]
      change m₀.val ((δ g : ℂ) •
        smoothContragredient τ g (b.toSmoothDual hτ.1 v)) = _
      rw [m₀.val.map_smul]
      change (δ g : ℂ) *
          (coefficientMap (smoothContragredient τ) m₀
            (b.toSmoothDual hτ.1 v)).val g = _
      rw [coefficient_hermitianDualFunctional]
    have hfirst :
        (coefficientMap τ ℓτ v).val g =
          (α g : ℂ) * (coefficientMap π ℓ v).val g := by
      change ℓ.val ((α g : ℂ) • π g v) = _
      exact ℓ.val.map_smul _ _
    rw [hsecond]
    calc
      (coefficientMap π ℓ v).val g *
          ((δ g : ℂ) * starRingEnd ℂ ((coefficientMap τ ℓτ v).val g)) =
          (χ g : ℂ)⁻¹ *
            ((coefficientMap τ ℓτ v).val g *
              starRingEnd ℂ ((coefficientMap τ ℓτ v).val g)) := by
        rw [hfirst]
        simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply,
          Units.val_mul, Units.val_inv_eq_inv_val]
        ring
      _ = _ := by
        rw [Complex.mul_conj']
        simp only [Complex.ofReal_pow]
        rfl

end Langlands.Whittaker
