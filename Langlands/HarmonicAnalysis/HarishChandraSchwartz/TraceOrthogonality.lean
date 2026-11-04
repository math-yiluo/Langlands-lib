import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily
import Langlands.Representation.Smooth.Contragredient.FixedVectorsProof
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof

/-! # The trace coefficient `ψ_H` in Schur orthogonality (proof of Waldspurger III.7.1)

In the proof of Proposition III.7.1 (printed pp. 274–275), Waldspurger integrates
`ψ_H(g) ⟨π(g) v, v̌⟩` over `A_G \ G`, where `ψ_H(g) = trace[ω̌(ε_H) ω̌(g) ω̌(ε_H)]`, and evaluates
the integral by III.1 (2) and (3): it vanishes if `π ≇ ω`, and equals `d(ω)⁻¹ ⟨v, v̌⟩` if
`π = ω` and `H` fixes `v`.

This module proves `ψ^{ω̌}_H(g) = ψ^ω_H(g⁻¹)` and both evaluations, for the integral over
`G/A` with an arbitrary central subgroup `A` as in `SchurOrthogonality`.
-/

noncomputable section

open MeasureTheory
open Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe u v w

section Contragredient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The trace coefficient of the smooth contragredient: `ψ^{ρ̌}_H(g) = ψ^ρ_H(g⁻¹)`. -/
theorem traceCoefficient_smoothContragredient (hρ : IsAdmissible ρ) (H : CompactOpenSubgroup G)
    (g : G) :
    traceCoefficient (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) H g =
      traceCoefficient ρ hρ.1 H g⁻¹ := by
  have : FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup) := hρ.2 H.1
  let R := LinearEquiv.ofBijective (smoothDualFixedRestriction ρ H.toSubgroup)
    (smoothDualFixedRestriction_bijective ρ hρ.1 H.1 H.2)
  have key : R.conj (Jacquet.compressedAction (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) H.1 H.2 g) =
      Module.Dual.transpose (R := ℂ) (Jacquet.compressedAction ρ hρ.1 H.1 H.2 g⁻¹) := by
    apply LinearMap.ext
    intro L
    apply LinearMap.ext
    intro x
    set m₀ := R.symm L with hm₀
    have hL : L = R m₀ := by rw [hm₀, LinearEquiv.apply_symm_apply]
    rw [hL, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change smoothDualFixedRestriction ρ H.toSubgroup
        (Jacquet.compressedAction (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
          H.1 H.2 g m₀) x =
      smoothDualFixedRestriction ρ H.toSubgroup m₀
        (Jacquet.compressedAction ρ hρ.1 H.1 H.2 g⁻¹ x)
    rw [smoothDualFixedRestriction_apply, smoothDualFixedRestriction_apply,
      Jacquet.compressedAction_apply, Jacquet.compressedAction_apply,
      Jacquet.smoothDualPairing_averageMap ρ hρ.1 H.1 H.2 m₀.property]
    let f : SmoothDual ρ →ₗ[ℂ] ℂ := (smoothDualPairing ρ).flip (x : V)
    have hf := Jacquet.map_averageMap_of_forall_eq (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) H.1 H.2 f (smoothContragredient ρ g m₀.val)
      (smoothDualPairing ρ (smoothContragredient ρ g m₀.val) x) (fun k => by
        change (smoothContragredient ρ (k : G) (smoothContragredient ρ g m₀.val)).val (x : V) =
          (smoothContragredient ρ g m₀.val).val (x : V)
        change (smoothContragredient ρ g m₀.val).val (ρ (k : G)⁻¹ (x : V)) = _
        have hx : ρ (k : G)⁻¹ (x : V) = x := x.property ⟨(k : G)⁻¹, H.toSubgroup.inv_mem k.2⟩
        rw [hx])
    change f (Compact.averageMap (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
      H.1 H.2 (smoothContragredient ρ g m₀.val)) = _
    rw [hf]
    rfl
  calc traceCoefficient (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) H g
      = LinearMap.trace ℂ _ (R.conj (Jacquet.compressedAction (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) H.1 H.2 g)) :=
        by
          have e := LinearMap.trace_conj' (R := ℂ)
            (M := fixedVectors (smoothContragredient ρ) H.toSubgroup)
            (N := Module.Dual ℂ (fixedVectors ρ H.toSubgroup))
            (Jacquet.compressedAction (smoothContragredient ρ)
            (isSmooth_smoothContragredient ρ) H.1 H.2 g) R
          exact e.symm
    _ = LinearMap.trace ℂ _ (Module.Dual.transpose (R := ℂ)
          (Jacquet.compressedAction ρ hρ.1 H.1 H.2 g⁻¹)) := by rw [key]
    _ = traceCoefficient ρ hρ.1 H g⁻¹ := by
          have e := LinearMap.trace_transpose' (R := ℂ)
            (Jacquet.compressedAction ρ hρ.1 H.1 H.2 g⁻¹)
          exact e

end Contragredient

section Orthogonality

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {W : Type w} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {ω : Representation ℂ G W} {χ : A →* ℂˣ}
  (hπ : ∀ (a : A) (x : V), π a x = (χ a : ℂ) • x)
  (hω : ∀ (a : A) (x : W), ω a x = (χ a : ℂ) • x)

/-- The function `gA ↦ ψ^ω_H(g⁻¹) ℓ(π(g) v)` on `G/A`, written as the finite sum of the
orthogonality integrands `ℓ(π(g) v) b_i^*(e_H ω(g⁻¹) b_i)` over a basis `b` of `W^H`. -/
def traceOrthogonalityIntegrand (hωa : IsAdmissible ω) (H : CompactOpenSubgroup G) (v : V)
    (ℓ : Module.Dual ℂ V) : G ⧸ A → ℂ :=
  haveI : FiniteDimensional ℂ (fixedVectors ω H.toSubgroup) := hωa.2 H.1
  ∑ i, orthogonalityIntegrand A hπ hω v ℓ
    ((Module.finBasis ℂ (fixedVectors ω H.toSubgroup) i : fixedVectors ω H.toSubgroup) : W)
    (fixedFunctional ω hωa.1 H
      ((Module.finBasis ℂ (fixedVectors ω H.toSubgroup)).coord i)).val

omit [A.Normal] in
theorem traceOrthogonalityIntegrand_mk (hωa : IsAdmissible ω) (H : CompactOpenSubgroup G)
    (v : V) (ℓ : Module.Dual ℂ V) (g : G) :
    traceOrthogonalityIntegrand A hπ hω hωa H v ℓ (QuotientGroup.mk g) =
      ℓ (π g v) * traceCoefficient ω hωa.1 H g⁻¹ := by
  have : FiniteDimensional ℂ (fixedVectors ω H.toSubgroup) := hωa.2 H.1
  rw [traceCoefficient_eq_sum ω hωa.1 H (Module.finBasis ℂ (fixedVectors ω H.toSubgroup)) g⁻¹,
    Finset.mul_sum]
  unfold traceOrthogonalityIntegrand
  rw [Finset.sum_apply]
  rfl

omit [A.Normal] in
/-- In Waldspurger's notation the integrand is `ψ^{ω̌}_H(g) ⟨π(g) v, ℓ⟩`. -/
theorem traceOrthogonalityIntegrand_mk_smoothContragredient (hωa : IsAdmissible ω)
    (H : CompactOpenSubgroup G) (v : V) (ℓ : Module.Dual ℂ V) (g : G) :
    traceOrthogonalityIntegrand A hπ hω hωa H v ℓ (QuotientGroup.mk g) =
      traceCoefficient (smoothContragredient ω) (isSmooth_smoothContragredient ω) H g *
        ℓ (π g v) := by
  rw [traceOrthogonalityIntegrand_mk, traceCoefficient_smoothContragredient ω hωa H g,
    mul_comm]

variable [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]

omit [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] [μ.IsInvInvariant] in
/-- The integral of the trace integrand is the sum of the orthogonality integrals
`I(v, ℓ, b_i, b_i^* ∘ e_H)`. -/
theorem integral_traceOrthogonalityIntegrand (hωa : IsAdmissible ω)
    (hint : ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : W) (ℓ₂ : SmoothDual ω),
      Integrable (orthogonalityIntegrand A hπ hω v₁ ℓ₁.val v₂ ℓ₂.val) μ)
    (H : CompactOpenSubgroup G) (v : V) (ℓ : SmoothDual π) :
    haveI : FiniteDimensional ℂ (fixedVectors ω H.toSubgroup) := hωa.2 H.1
    ∫ q, traceOrthogonalityIntegrand A hπ hω hωa H v ℓ.val q ∂μ =
      ∑ i, orthogonalityIntegral A μ hπ hω v ℓ
        ((Module.finBasis ℂ (fixedVectors ω H.toSubgroup) i : fixedVectors ω H.toSubgroup) : W)
        (fixedFunctional ω hωa.1 H
          ((Module.finBasis ℂ (fixedVectors ω H.toSubgroup)).coord i)) := by
  have : FiniteDimensional ℂ (fixedVectors ω H.toSubgroup) := hωa.2 H.1
  unfold traceOrthogonalityIntegrand orthogonalityIntegral
  simp only [Finset.sum_apply]
  exact integral_finsetSum _ fun i _ => hint _ _ _ _

variable (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

include hcof in
/-- **Proof of III.7.1, first case.** If `π` and `ω` are irreducible admissible and not
equivalent and all orthogonality integrands are integrable, then
`∫_{G/A} ψ^{ω̌}_H(g) ⟨π(g) v, ℓ⟩ dg = 0`. -/
theorem integral_traceOrthogonalityIntegrand_eq_zero (hπa : IsAdmissible π)
    (hωa : IsAdmissible ω) (hiπ : π.IsIrreducible) (hiω : ω.IsIrreducible)
    (hne : IsEmpty (π.Equiv ω))
    (hint : ∀ (v₁ : V) (ℓ₁ : SmoothDual π) (v₂ : W) (ℓ₂ : SmoothDual ω),
      Integrable (orthogonalityIntegrand A hπ hω v₁ ℓ₁.val v₂ ℓ₂.val) μ)
    (H : CompactOpenSubgroup G) (v : V) (ℓ : SmoothDual π) :
    ∫ q, traceOrthogonalityIntegrand A hπ hω hωa H v ℓ.val q ∂μ = 0 := by
  rw [integral_traceOrthogonalityIntegrand A hπ hω μ hωa hint]
  exact Finset.sum_eq_zero fun i _ =>
    orthogonalityIntegral_eq_zero_of_integrable A μ hπ hω hint hcof hπa hωa hiπ hiω hne _ _ _ _

variable (hA : A ≤ Subgroup.center G)

include hcof in
/-- **Proof of III.7.1, second case.** For `ω` irreducible and square integrable modulo `A`,
`∫_{G/A} ψ^{ω̌}_H(g) ⟨ω(g) v, ℓ⟩ dg = d(ω)⁻¹ ⟨e_H v, ℓ⟩`. -/
theorem integral_traceOrthogonalityIntegrand_eq_formalDegree
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ω μ) (hi : ω.IsIrreducible)
    (H : CompactOpenSubgroup G) (v : W) (ℓ : SmoothDual ω) :
    ∫ q, traceOrthogonalityIntegrand A hω hω hsq.1 H v ℓ.val q ∂μ =
      (formalDegree A hA μ hω hcof hsq hi : ℂ)⁻¹ *
        ℓ.val (Compact.averageMap ω hsq.1.1 H.1 H.2 v) := by
  have : FiniteDimensional ℂ (fixedVectors ω H.toSubgroup) := hsq.1.2 H.1
  set b := Module.finBasis ℂ (fixedVectors ω H.toSubgroup)
  rw [integral_traceOrthogonalityIntegrand A hω hω μ hsq.1
    (integrable_orthogonalityIntegrand A hA μ hω hω hsq hsq)]
  simp_rw [orthogonalityIntegral_eq_formalDegree A hA μ hω hcof hsq hi]
  have hsum : ∑ i, (fixedFunctional ω hsq.1.1 H (b.coord i)).val v • ((b i : _) : W) =
      Compact.averageMap ω hsq.1.1 H.1 H.2 v := by
    have h := b.sum_repr (averageProjection ω hsq.1.1 H v)
    have h' := congrArg (fun x : fixedVectors ω H.toSubgroup => (x : W)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    rw [averageProjection_apply] at h'
    rw [← h']
    rfl
  rw [← hsum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

include hcof in
/-- For `v` fixed by `H`: `∫_{G/A} ψ^{ω̌}_H(g) ⟨ω(g) v, ℓ⟩ dg = d(ω)⁻¹ ⟨v, ℓ⟩`. -/
theorem integral_traceOrthogonalityIntegrand_eq_formalDegree_of_mem
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ω μ) (hi : ω.IsIrreducible)
    (H : CompactOpenSubgroup G) {v : W} (hv : v ∈ fixedVectors ω H.toSubgroup)
    (ℓ : SmoothDual ω) :
    ∫ q, traceOrthogonalityIntegrand A hω hω hsq.1 H v ℓ.val q ∂μ =
      (formalDegree A hA μ hω hcof hsq hi : ℂ)⁻¹ * ℓ.val v := by
  rw [integral_traceOrthogonalityIntegrand_eq_formalDegree A hω μ hcof hA hsq hi,
    Compact.averageMap_id ω hsq.1.1 H.1 H.2 v hv]

end Orthogonality

end Langlands.HarishChandraSchwartz
