import Langlands.Representation.Induction.CompactScalarProof
import Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar
import Langlands.Representation.GodementJacquet.Zeta

/-! # The actual compact integral formula for normalized induced coefficients -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.GodementJacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The scalar compact-picture integrand, with the first induced section in the
induction of the smooth dual and the second section translated on the right. -/
def compactInducedCoefficientKernel
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((smoothContragredient σ).comp (B.leviProjection F.Carrier))) →
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) →
      GeneralLinear n F.Carrier → GeneralLinear n F.Carrier → ℂ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  exact fun h f g k =>
    smoothDualPairing σ (Induction.eval _ _ h k) (Induction.eval _ _ f (k * g))

/-- In every positive rank there is one compact open Iwasawa subgroup with a
Haar probability measure for which every smooth functional on an admissible
normalized induction has the actual compact coefficient formula. -/
theorem exists_compactInducedCoefficientFormula (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
      IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
      (∀ g : GeneralLinear n F.Carrier,
        ∃ (q : B.parabolic F.Carrier) (k : K),
          g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier)) ∧
      (letI : MeasurableSpace K := borel K
       ∃ μ : Measure K, μ.IsHaarMeasure ∧ IsProbabilityMeasure μ ∧
         ∀ (σ : Representation ℂ (B.Levi F.Carrier) V), IsAdmissible σ →
           ∃ E : Representation.Equiv
               (smoothContragredient (T.normalizedParabolicInduced B σ))
               (T.normalizedParabolicInduced B (smoothContragredient σ)),
             ∀ (ℓ : SmoothDual (T.normalizedParabolicInduced B σ))
               (f : Induction.SmoothFunctions (B.parabolic F.Carrier)
                 (twist (T.parabolicHalfModulus B)
                   (σ.comp (B.leviProjection F.Carrier))))
               (g : GeneralLinear n F.Carrier),
               Integrable (fun k : K =>
                 compactInducedCoefficientKernel T B σ (E ℓ) f g k) μ ∧
               matrixCoefficient (T.normalizedParabolicInduced B σ)
                   (smoothDualPairing _ ℓ) f g =
                 ∫ k : K, compactInducedCoefficientKernel T B σ (E ℓ) f g k ∂μ) := by
  let := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  have := T.generalLinearNonarchimedean n
  have := T.generalLinearLocallyCompactSpace n
  have := T.leviNonarchimedean B
  have := T.leviLocallyCompactSpace B
  obtain ⟨K, hKc, hPK, hμ⟩ := glParabolicCompactScalarIntegral p F T n hn B
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μ, hHaar, hprob, hscalar⟩ := hμ
  let := hHaar
  let := hprob
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let δ : B.parabolic F.Carrier → ℝ≥0 := fun q =>
    (T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0)
  have hm : Continuous (B.leviProjection F.Carrier) := (T.blockLeviProjection B).continuous
  have hδ : ∀ q : B.parabolic F.Carrier,
      (T.parabolicHalfModulus B q : ℂ) * T.parabolicHalfModulus B q =
        ((δ q : ℝ) : ℂ) := by
    intro q
    have h := congrArg Units.val (T.leviHalfModulus_sq B (B.leviProjection F.Carrier q))
    rw [Units.val_pow_eq_pow_val, Jacquet.complexCharacter_apply, sq] at h
    exact h
  have hcofM : ∀ H : OpenSubgroup (B.Levi F.Carrier),
      ∃ L : OpenSubgroup (B.Levi F.Carrier),
        IsCompact (L : Set (B.Levi F.Carrier)) ∧ L ≤ H := by
    intro H
    obtain ⟨L, hL, hLH⟩ :=
      compactOpenSubgroupBasis (B.Levi F.Carrier)
        (H : Set (B.Levi F.Carrier)) H.mem_nhds_one
    exact ⟨L, hL, fun _ hx => hLH hx⟩
  refine ⟨K, hKc, hPK, μ, hHaar, hprob, ?_⟩
  intro σ hσ
  obtain ⟨E, hE⟩ := Induction.exists_integralDualEquiv
    (B.parabolic F.Carrier) (B.leviProjection F.Carrier) (T.parabolicHalfModulus B)
    δ K.toSubgroup μ hm (T.isOpen_ker_parabolicHalfModulus B) hδ hcofM hscalar σ hσ.1
    (Parabolic.normalizedInductionAdmissibility F T B V σ hσ)
  refine ⟨E, fun ℓ f g => ?_⟩
  have hloc := Induction.bilinearPairing_isLocallyConstant
    (B.parabolic F.Carrier) _ _ (smoothDualPairing σ) (E ℓ)
    (T.normalizedParabolicInduced B σ g f)
  have hcont : Continuous (fun k : K =>
      compactInducedCoefficientKernel T B σ (E ℓ) f g k) :=
    hloc.continuous.comp continuous_subtype_val
  exact ⟨hcont.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact,
    hE ℓ (T.normalizedParabolicInduced B σ g f)⟩

end Langlands.GodementJacquet
