import Langlands.Representation.Plancherel.StandardIntertwiningScalarBounds
import Langlands.Representation.Category.Twist

/-! # A common growth exponent for character-twisted scalar convergence -/

noncomputable section

namespace Langlands.Plancherel

universe uG uV

section Coefficients

variable {L : Type uG} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (A : SmoothRep.{0, uG, uV} ℂ L)
  (χ : L →* ℂˣ) (hχ : IsOpen (χ.ker : Set L))

/-- The smooth-dual twist equivalence preserves the actual functional, so
twisting multiplies its coefficient norm by the character norm. -/
theorem twistCoefficient_norm (v : A)
    (ℓ : SmoothDual (A.twist χ hχ).representation) (m : L) :
    ‖ℓ.val ((A.twist χ hχ).representation m v)‖ =
      ‖(χ m : ℂ)‖ *
        ‖(smoothContragredientTwistEquiv χ A.representation hχ ℓ).val
          (A.representation m v)‖ := by
  change ‖ℓ.val ((χ m : ℂ) • A.representation m v)‖ = _
  rw [map_smul, norm_smul]
  rfl

/-- A common envelope for the original coefficients gives the character norm
times that same envelope for every open-kernel twist. -/
theorem coefficientEnvelope_twist (ξ : L → ℝ)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m) :
    ∀ (v : A.twist χ hχ) (ℓ : SmoothDual (A.twist χ hχ).representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m,
        ‖ℓ.val ((A.twist χ hχ).representation m v)‖ ≤
          C * (‖(χ m : ℂ)‖ * ξ m) := by
  intro v ℓ
  obtain ⟨C, hC, hb⟩ := hcoeff v
    (smoothContragredientTwistEquiv χ A.representation hχ ℓ)
  refine ⟨C, hC, fun m => ?_⟩
  rw [twistCoefficient_norm A χ hχ]
  exact (mul_le_mul_of_nonneg_left (hb m) (norm_nonneg _)).trans_eq (by ring)

end Coefficients

namespace StandardIntertwining

open Aubert.General Induction MeasureTheory

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)

/-- The actual source half-character times a fixed power envelope and a
varying character norm, evaluated on supplied quotient coordinates. -/
def twistIwasawaWeight (H : M → ℝ) (d : ℕ) (χ : M →* ℂˣ)
    (p : QuotientSpace (U := U) U' → P) :
    QuotientSpace (U := U) U' → ℝ :=
  iwasawaWeight h hU U' (fun m => ‖(χ m : ℂ)‖ * H m ^ d) p

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)

/-- One exponent chosen for the original representation works before varying
the character. Only integrability of its explicitly twisted scalar weight
remains in this convergence reduction. -/
theorem exists_exponent_scalarDomain_eq_top_twist
    (hK : IsCompact (K : Set G))
    (H : M → ℝ) (hH : ∀ m, 1 ≤ H m)
    (hgrowth : ∃ d : ℕ,
      ∀ (v : A) (ℓ : SmoothDual A.representation),
        ∃ C : ℝ, 0 < C ∧ ∀ m,
          ‖ℓ.val (A.representation m v)‖ ≤ C * H m ^ d)
    (p : QuotientSpace (U := U) U' → P) (k : QuotientSpace (U := U) U' → K)
    (hfactor : ∀ q, ∃ u' : U', Quotient.mk _ u' = q ∧
      (u' : G) = (p q : G) * (k q : G)) :
    ∃ d : ℕ, ∀ (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)),
      MeasureTheory.Integrable (twistIwasawaWeight h hU U' H d χ p) ν →
        scalarDomain h hU U' (A.twist χ hχ) ν = ⊤ := by
  obtain ⟨d, hd⟩ := hgrowth
  refine ⟨d, fun χ hχ hi => ?_⟩
  exact scalarDomain_eq_top_of_integrable_iwasawaWeight h hU U'
    (A.twist χ hχ) ν K hK
    (fun m => ‖(χ m : ℂ)‖ * H m ^ d)
    (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg (le_trans zero_le_one (hH m)) d))
    (coefficientEnvelope_twist A χ hχ (fun m => H m ^ d) hd) p k hfactor hi

end StandardIntertwining

end Langlands.Plancherel
