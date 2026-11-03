import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Hecke.FiniteSampling
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite character coefficients for actual compact-section Hecke matrix entries. -/

noncomputable section

namespace Langlands.Induction

open HarmonicAnalysis MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The existing compact section for the twisted coefficient action, using the
same underlying fixed vector whenever the character is trivial on its stabilizer. -/
def twistedDoubleCosetSection (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    (v : fixedVectors σ (conjOpenSubgroup P K x).toSubgroup)
    (χ : P →* ℂˣ) (hχ : (conjOpenSubgroup P K x).toSubgroup ≤ χ.ker) :
    CompactFunctions P (twist χ σ) :=
  compactDoubleCosetSection P (twist χ σ) K hK x v.val (by
    rw [fixedVectors_twist_eq_of_le_ker χ σ _ hχ]
    exact v.property)

/-- Finitely supported character coefficients of one compact-section value.
The point factorization, hence the coefficients, is chosen before the character. -/
def compactSectionTwistCoefficients (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (x : G) (v : V) (L : V →ₗ[ℂ] ℂ) (z : G) : P →₀ ℂ := by
  classical
  exact if h : ∃ p : P, ∃ k : K, z = (p : G) * x * (k : G) then
    Finsupp.single h.choose (L (σ h.choose v))
  else 0

/-- Evaluating the finite coefficients at any allowed character recovers the
actual twisted compact section at every point. -/
theorem compactSectionTwistCoefficients_eval
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    (v : fixedVectors σ (conjOpenSubgroup P K x).toSubgroup)
    (L : V →ₗ[ℂ] ℂ) (z : G)
    (χ : P →* ℂˣ) (hχ : (conjOpenSubgroup P K x).toSubgroup ≤ χ.ker) :
    Finsupp.linearCombination ℂ (fun p : P => (χ p : ℂ))
        (compactSectionTwistCoefficients P σ K x v.val L z) =
      L (eval P (twist χ σ) (twistedDoubleCosetSection P σ K hK x v χ hχ).val z) := by
  classical
  by_cases hz : ∃ p : P, ∃ k : K, z = (p : G) * x * (k : G)
  · rw [compactSectionTwistCoefficients, dite_eq_left hz, Finsupp.linearCombination_single]
    have he := hz.choose_spec.choose_spec
    conv_rhs => rw [he]
    change L (σ hz.choose v.val) • (χ hz.choose : ℂ) =
      L (eval P (twist χ σ)
        (compactDoubleCosetSection P (twist χ σ) K hK x v.val _).val
          ((hz.choose : G) * x * (hz.choose_spec.choose : G)))
    rw [compactDoubleCosetSection_apply]
    simp [twist, mul_comm]
  · have hzero : eval P (twist χ σ)
        (twistedDoubleCosetSection P σ K hK x v χ hχ).val z = 0 := by
      by_contra hn
      obtain ⟨k, hk, he⟩ :=
        compactDoubleCosetSection_support_subset P (twist χ σ) K hK x v.val
          (by
            rw [fixedVectors_twist_eq_of_le_ker χ σ _ hχ]
            exact v.property) ⟨z, hn, rfl⟩
      have hp : z * (x * k)⁻¹ ∈ P :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact he)
      exact hz ⟨⟨z * (x * k)⁻¹, hp⟩, ⟨k, hk⟩, by simp [mul_assoc]⟩
    rw [compactSectionTwistCoefficients, dite_eq_right hz, map_zero, hzero, map_zero]

variable [MeasurableSpace G] [OpensMeasurableSpace G]

/-- Finitely supported character coefficients of an actual Hecke matrix entry
on a compact double-coset section. -/
def integratedCompactSectionTwistCoefficients
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (f : SchwartzBruhat G)
    (hf : ∀ (k : K) g, f (g * (k : G)) = f g)
    (x : G) (v : V) (L : V →ₗ[ℂ] ℂ) (y : G) : P →₀ ℂ :=
  let S := Hecke.fixedLevelActionSamples μ K f hf
  ∑ i, S.coefficients i •
    compactSectionTwistCoefficients P σ K x v L (y * S.points i)

/-- The same finite character expression computes the actual Hecke matrix
entry for every twist trivial on the indicated compact-section stabilizer. -/
theorem integratedCompactSectionTwistCoefficients_eval
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) (hf : ∀ (k : K) g, f (g * (k : G)) = f g)
    (x : G) (v : fixedVectors σ (conjOpenSubgroup P K x).toSubgroup)
    (L : V →ₗ[ℂ] ℂ) (y : G)
    (χ : P →* ℂˣ) (hχ : (conjOpenSubgroup P K x).toSubgroup ≤ χ.ker) :
    Finsupp.linearCombination ℂ (fun p : P => (χ p : ℂ))
        (integratedCompactSectionTwistCoefficients μ P σ K f hf x v.val L y) =
      L (eval P (twist χ σ)
        (Hecke.integratedAction μ (smoothInduced P (twist χ σ))
          (smoothInduced_smooth P (twist χ σ)) f
          (twistedDoubleCosetSection P σ K hK x v χ hχ).val) y) := by
  let S := Hecke.fixedLevelActionSamples μ K f hf
  let s := twistedDoubleCosetSection P σ K hK x v χ hχ
  let E : SmoothFunctions P (twist χ σ) →ₗ[ℂ] ℂ :=
    { toFun := fun F => L (eval P (twist χ σ) F y)
      map_add' := fun _ _ => L.map_add _ _
      map_smul' := fun _ _ => L.map_smul _ _ }
  have hs : s.val ∈ fixedVectors (smoothInduced P (twist χ σ)) K.toSubgroup := by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact compactDoubleCosetSection_mul P (twist χ σ) K hK x v.val
      (by
        rw [fixedVectors_twist_eq_of_le_ker χ σ _ hχ]
        exact v.property) k z
  change Finsupp.linearCombination ℂ (fun p : P => (χ p : ℂ))
    (∑ i, S.coefficients i • compactSectionTwistCoefficients P σ K x v.val L
      (y * S.points i)) =
    E (Hecke.integratedAction μ (smoothInduced P (twist χ σ))
      (smoothInduced_smooth P (twist χ σ)) f s.val)
  rw [Hecke.fixedLevelActionSamples_action μ K f hf
    (smoothInduced P (twist χ σ)) (smoothInduced_smooth P (twist χ σ)) s.val hs,
    map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  apply congrArg (S.coefficients i • ·)
  exact compactSectionTwistCoefficients_eval P σ K hK x v L (y * S.points i) χ hχ

end Langlands.Induction
