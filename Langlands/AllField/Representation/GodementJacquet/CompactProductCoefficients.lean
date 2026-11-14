import Langlands.Representation.GodementJacquet.CompactProductCoefficients
import Langlands.AllField.Representation.GodementJacquet.CompactInducedCoefficients
import Langlands.AllField.Representation.Induction.BlockFactors
/-! # Uniform compact expansions of product-induced pairings -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion
open Langlands.AllField.GodementJacquet

universe uI uG uV uX uF

section CompactFamily


end CompactFamily

section Padic

open _root_.MeasureTheory

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The compact two-section pairing before integration over the compact group. -/
def compactProductPairingKernel
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((smoothContragredient (B.blockTensor σ)).comp (B.leviProjection F))) →
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F))) →
      GeneralLinear n F → GeneralLinear n F → B.Levi F → ℂ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  exact fun h f k k' m => smoothDualPairing (B.blockTensor σ)
    (Induction.eval _ _ h k) (B.blockTensor σ m (Induction.eval _ _ f k'))

/-- The actual compact-section pairing has one finite expansion, uniform in
both compact arguments and the Levi element, into actual block coefficients. -/
theorem exists_compactProductPairing_expansion
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    (∀ i, IsAdmissible (σ i)) →
      ∀ K : OpenSubgroup (GeneralLinear n F),
        IsCompact (K : Set (GeneralLinear n F)) →
        ∀ (h : Induction.SmoothFunctions (B.parabolic F)
            (twist (T.parabolicHalfModulus B)
              ((smoothContragredient (B.blockTensor σ)).comp (B.leviProjection F))))
          (f : Induction.SmoothFunctions (B.parabolic F)
            (twist (T.parabolicHalfModulus B)
              ((B.blockTensor σ).comp (B.leviProjection F)))),
          ∃ (N : ℕ) (φ : Fin N → HarmonicAnalysis.SchwartzBruhat (K × K))
            (ℓ : Fin N → ∀ i, SmoothDual (σ i)) (w : Fin N → ∀ i, V i),
            ∀ (k k' : K) (m : B.Levi F),
              compactProductPairingKernel T B σ h f k k' m =
                ∑ j : Fin N, φ j (k, k') * ∏ i,
                  matrixCoefficient (σ i) (smoothDualPairing (σ i) (ℓ j i))
                    (w j i) (m i) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let : ∀ i : Fin B.length, IsTopologicalGroup (GeneralLinear (B.size i) F) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  intro hσ K hK h f
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcof : ∀ i (H : OpenSubgroup (GeneralLinear (B.size i) F)),
      ∃ L : OpenSubgroup (GeneralLinear (B.size i) F),
        IsCompact (L : Set (GeneralLinear (B.size i) F)) ∧ L ≤ H := by
    intro i H
    let := T.generalLinearNonarchimedean (B.size i)
    let := T.generalLinearLocallyCompactSpace (B.size i)
    obtain ⟨L, hL, hLH⟩ := compactOpenSubgroupBasis _ _ H.mem_nhds_one
    exact ⟨L, hL, fun _ hx => hLH hx⟩
  let L : K × K → SmoothDual (B.blockTensor σ) := fun x => Induction.eval _ _ h x.1
  let v : K × K → PiTensorProduct ℂ V := fun x => Induction.eval _ _ f x.2
  have hL : IsLocallyConstant L :=
    (Induction.eval_isLocallyConstant _ _ h).comp_continuous
      (continuous_subtype_val.comp continuous_fst)
  have hv : IsLocallyConstant v :=
    (Induction.eval_isLocallyConstant _ _ f).comp_continuous
      (continuous_subtype_val.comp continuous_snd)
  obtain ⟨N, φ, ℓ, w, hexp⟩ :=
    exists_uniform_compact_productCoefficient_expansion σ hσ hcof L v hL hv
  exact ⟨N, φ, ℓ, w, fun k k' m => hexp (k, k') m⟩

/-- The compact coefficient formula for product induction, with all tensor
admissibility hypotheses discharged from admissibility of the blocks. -/
theorem exists_compactProductCoefficientFormula (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    ∃ K : OpenSubgroup (GeneralLinear n F),
      IsCompact (K : Set (GeneralLinear n F)) ∧
      (∀ g : GeneralLinear n F,
        ∃ (q : B.parabolic F) (k : K),
          g = (q : GeneralLinear n F) * (k : GeneralLinear n F)) ∧
      (letI : MeasurableSpace K := borel K
       ∃ μ : Measure K, μ.IsHaarMeasure ∧ IsProbabilityMeasure μ ∧
         ∀ (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)),
           (∀ i, IsAdmissible (σ i)) →
           ∃ E : Representation.Equiv
               (smoothContragredient (T.normalizedProductInduced B σ))
               (T.normalizedParabolicInduced B (smoothContragredient (B.blockTensor σ))),
             ∀ (ℓ : SmoothDual (T.normalizedProductInduced B σ))
               (f : Induction.SmoothFunctions (B.parabolic F)
                 (twist (T.parabolicHalfModulus B)
                   ((B.blockTensor σ).comp (B.leviProjection F))))
               (g : GeneralLinear n F),
               Integrable (fun k : K =>
                 compactInducedCoefficientKernel T B (B.blockTensor σ) (E ℓ) f g k) μ ∧
               matrixCoefficient (T.normalizedProductInduced B σ)
                   (smoothDualPairing _ ℓ) f g =
                 ∫ k : K,
                   compactInducedCoefficientKernel T B (B.blockTensor σ) (E ℓ) f g k ∂μ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  obtain ⟨K, hK, hPK, hμ⟩ :=
    exists_compactInducedCoefficientFormula (V := PiTensorProduct ℂ V) T B hn
  let : MeasurableSpace K := borel K
  obtain ⟨μ, hHaar, hprob, hformula⟩ := hμ
  refine ⟨K, hK, hPK, μ, hHaar, hprob, fun σ hσ => ?_⟩
  exact hformula (B.blockTensor σ) (FiniteTensor.isAdmissible_external σ hσ)

end Padic

end Langlands.AllField.GodementJacquet
