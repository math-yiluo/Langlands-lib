import Langlands.Global.AdelicRegularizedConeFourierBoundary

/-! # Presentation independence of the regularized cone integral -/

noncomputable section

open AlgebraicGeometry Filter MeasureTheory Set
open scoped Classical Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Analysis

variable {ι : Type*} [Fintype ι]

private theorem shifted_sum_regularizedOrthantTerm_eq_integral {κ : Type*}
    (s : Finset κ) (z : κ → ι → ℂ) (P : κ → MvPolynomial ι ℂ) (b : ι → ℝ)
    (hunitary : ∀ k ∈ s, ∀ i, (z k i).re = 0) {t : ℝ} (ht : 0 < t) :
    (∑ k ∈ s, regularizedOrthantTerm b (P k) (fun i => z k i + (t : ℂ))) =
      ∫ x in translatedOrientedOrthant (fun _ => 1) b,
        Complex.exp (-(t : ℂ) * ∑ i, (x i : ℂ)) *
          ∑ k ∈ s, Complex.exp (∑ i, ((-x) i : ℂ) * z k i) *
            MvPolynomial.eval (fun i => ((-x) i : ℂ)) (P k) := by
  let shifted (k : κ) (i : ι) : ℂ := z k i + (t : ℂ)
  let kernel (k : κ) (x : ι → ℝ) : ℂ :=
    Complex.exp (∑ i, -shifted k i * (x i : ℂ)) *
      MvPolynomial.eval (fun i => -(x i : ℂ)) (P k)
  let cone := translatedOrientedOrthant (fun _ => 1) b
  have hsign : orthantSign (fun _ : ι => 1) = 1 := by simp [orthantSign]
  have hLaplace (k : κ) (hk : k ∈ s) : IntegrableOn (kernel k) cone ∧
      regularizedOrthantTerm b (P k) (shifted k) = ∫ x in cone, kernel k x := by
    have hre (i : ι) : (shifted k i).re = t := by simp [shifted, hunitary k hk i]
    have h := translatedOrthant_polynomialLaplace (d := fun _ => 1) (z := shifted k)
      (fun i => (hre i).trans_ne ht.ne') (fun i => by simp [hre i, ht]) b (P k)
    simpa only [kernel, cone, regularizedOrthantTerm, hsign, one_mul] using h
  change (∑ k ∈ s, regularizedOrthantTerm b (P k) (shifted k)) = _
  calc
    _ = ∑ k ∈ s, ∫ x in cone, kernel k x := Finset.sum_congr rfl fun k hk => (hLaplace k hk).2
    _ = ∫ x in cone, ∑ k ∈ s, kernel k x := (integral_finsetSum s fun k hk => (hLaplace k hk).1).symm
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      dsimp only
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [kernel, shifted, Pi.neg_apply, Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add]
      have hphase : (∑ i, -(z k i + (t : ℂ)) * (x i : ℂ)) =
          -(t : ℂ) * (∑ i, (x i : ℂ)) + ∑ i, -(x i : ℂ) * z k i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hphase]

private theorem continuousAt_regularizedOrthantTerm_add
    (b : ι → ℝ) (P : MvPolynomial ι ℂ) {z : ι → ℂ} (hz : ∀ i, z i ≠ 0) :
    ContinuousAt (fun t : ℝ => regularizedOrthantTerm b P (fun i => z i + (t : ℂ))) 0 := by
  unfold regularizedOrthantTerm negativeOrthantRegularizedIntegral
  refine ContinuousAt.mul (by fun_prop) ?_
  apply tendsto_finsetSum
  intro k _
  refine ContinuousAt.mul continuousAt_const ?_
  apply tendsto_finsetProd
  intro i _
  have h : ContinuousAt (fun t : ℝ => z i + (t : ℂ)) 0 := by fun_prop
  exact (hasDerivAt_orthantFactor (hz i) (k i)).continuousAt.comp_of_eq h (by simp)

private theorem tendsto_shifted_sum_regularizedOrthantTerm {κ : Type*}
    (s : Finset κ) (z : κ → ι → ℂ) (P : κ → MvPolynomial ι ℂ) (b : ι → ℝ)
    (hregular : ∀ k ∈ s, ∀ i, z k i ≠ 0) :
    Tendsto (fun t : ℝ => ∑ k ∈ s, regularizedOrthantTerm b (P k) (fun i => z k i + (t : ℂ)))
      (𝓝[>] 0) (𝓝 (∑ k ∈ s, regularizedOrthantTerm b (P k) (z k))) := by
  have h : ContinuousAt
      (fun t : ℝ => ∑ k ∈ s, regularizedOrthantTerm b (P k) (fun i => z k i + (t : ℂ))) 0 :=
    tendsto_finsetSum s fun k hk => continuousAt_regularizedOrthantTerm_add b (P k) (hregular k hk)
  simpa only [Complex.ofReal_zero, add_zero] using (h.continuousWithinAt (s := Ioi (0 : ℝ))).tendsto

/-- Finite regular unitary polynomial expansions that agree pointwise have equal regularized
integrals at every translated vertex. The two finite index sets can have different types. -/
def RegularizedOrthantSumExtensionalityStatement {κ₁ κ₂ : Type*}
    (s₁ : Finset κ₁) (s₂ : Finset κ₂) (z₁ : κ₁ → ι → ℂ) (z₂ : κ₂ → ι → ℂ)
    (P₁ : κ₁ → MvPolynomial ι ℂ) (P₂ : κ₂ → MvPolynomial ι ℂ) : Prop :=
  (∀ k ∈ s₁, ∀ i, (z₁ k i).re = 0) → (∀ k ∈ s₂, ∀ i, (z₂ k i).re = 0) →
  (∀ k ∈ s₁, ∀ i, z₁ k i ≠ 0) → (∀ k ∈ s₂, ∀ i, z₂ k i ≠ 0) →
  (∀ c : ι → ℝ,
    (∑ k ∈ s₁, Complex.exp (∑ i, (c i : ℂ) * z₁ k i) *
      MvPolynomial.eval (fun i => (c i : ℂ)) (P₁ k)) =
    (∑ k ∈ s₂, Complex.exp (∑ i, (c i : ℂ) * z₂ k i) *
      MvPolynomial.eval (fun i => (c i : ℂ)) (P₂ k))) →
  ∀ b : ι → ℝ, (∑ k ∈ s₁, regularizedOrthantTerm b (P₁ k) (z₁ k)) =
    ∑ k ∈ s₂, regularizedOrthantTerm b (P₂ k) (z₂ k)

/-- A common positive real shift gives equal convergent Laplace integrals, and regularity allows
both closed formulas to tend to their values at zero shift. -/
theorem sum_regularizedOrthantTerm_eq_of_eval_eq {κ₁ κ₂ : Type*}
    (s₁ : Finset κ₁) (s₂ : Finset κ₂) (z₁ : κ₁ → ι → ℂ) (z₂ : κ₂ → ι → ℂ)
    (P₁ : κ₁ → MvPolynomial ι ℂ) (P₂ : κ₂ → MvPolynomial ι ℂ) :
    RegularizedOrthantSumExtensionalityStatement s₁ s₂ z₁ z₂ P₁ P₂ := by
  intro hunitary₁ hunitary₂ hregular₁ hregular₂ heval b
  refine tendsto_nhds_unique_of_eventuallyEq
    (tendsto_shifted_sum_regularizedOrthantTerm s₁ z₁ P₁ b hregular₁)
    (tendsto_shifted_sum_regularizedOrthantTerm s₂ z₂ P₂ b hregular₂) ?_
  refine eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => ?_)
  change 0 < t at ht
  dsimp only
  rw [shifted_sum_regularizedOrthantTerm_eq_integral s₁ z₁ P₁ b hunitary₁ ht,
    shifted_sum_regularizedOrthantTerm_eq_integral s₂ z₂ P₂ b hunitary₂ ht]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  dsimp only
  rw [heval (-x)]

namespace StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints

variable {F : Type} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {𝓕 : StandardParabolicFamily F G} {Q : StandardIndex F G 𝓕.i 𝓕.ν}

/-- Equal regular expansions of a normalized pairing give the same regularized cone integral. -/
theorem UnitaryPairingExpansion.regularizedConeIntegral_eq_of_eval_eq
    {e₁ e₂ : 𝓕.UnitaryPairingExpansion Q} (h₁ : e₁.IsRegular) (h₂ : e₂.IsRegular)
    (heval : ∀ c, e₁.eval c = e₂.eval c) (Tp : V 𝓕.T) :
    e₁.regularizedConeIntegral Tp = e₂.regularizedConeIntegral Tp := by
  have hunitary (e : 𝓕.UnitaryPairingExpansion Q) (lam) (hlam : lam ∈ e.exponents) (i) :
      (𝓕.corootValue Q lam i).re = 0 := by
    simp [corootValue, complexParameterPairing_re, e.unitary lam hlam]
  exact sum_regularizedOrthantTerm_eq_of_eval_eq e₁.exponents e₂.exponents
    (𝓕.corootValue Q) (𝓕.corootValue Q) e₁.coefficient e₂.coefficient
    (hunitary e₁) (hunitary e₂) h₁ h₂ heval (𝓕.weightCoordinate Q Tp)

end StandardParabolicFamily

end Langlands.Global
