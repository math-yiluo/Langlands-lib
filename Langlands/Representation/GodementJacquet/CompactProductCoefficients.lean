import Langlands.Representation.GodementJacquet.TensorCoefficients
import Langlands.Representation.GodementJacquet.CompactInducedCoefficients
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.HarmonicAnalysis.CompactCosetExpansion

/-! # Uniform compact expansions of product-induced pairings -/

noncomputable section

namespace Langlands.GodementJacquet

universe uI uG uV uX uF

section CompactFamily

variable {ι : Type uI} [Fintype ι]
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- A locally constant family of actual tensor pairings on a compact space has
one finite Schwartz expansion in products of factor coefficients. -/
theorem exists_uniform_compact_productCoefficient_expansion
    {X : Type uX} [TopologicalSpace X] [CompactSpace X]
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (hρ : ∀ i, IsAdmissible (ρ i))
    (hcof : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K)
    (L : X → SmoothDual (FiniteTensor.external ρ))
    (v : X → PiTensorProduct ℂ V)
    (hL : IsLocallyConstant L) (hv : IsLocallyConstant v) :
    ∃ (N : ℕ) (φ : Fin N → HarmonicAnalysis.SchwartzBruhat X)
      (ℓ : Fin N → ∀ i, SmoothDual (ρ i)) (w : Fin N → ∀ i, V i),
      ∀ x g, smoothDualPairing (FiniteTensor.external ρ) (L x)
          (FiniteTensor.external ρ g (v x)) =
        ∑ j : Fin N, φ j x * ∏ i,
          matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ j i)) (w j i) (g i) := by
  classical
  let H : X → (∀ i, G i) → ℂ := fun x =>
    matrixCoefficient (FiniteTensor.external ρ) (smoothDualPairing _ (L x)) (v x)
  have hH : IsLocallyConstant H := hL.comp₂ hv (fun ℓ w =>
    matrixCoefficient (FiniteTensor.external ρ) (smoothDualPairing _ ℓ) w)
  obtain ⟨q, φ, r, hr⟩ := HarmonicAnalysis.exists_finite_schwartz_expansion H hH
    (isClosed_tsupport H).isCompact
  have hsamples (j : Fin q) :
      ∃ (S : Finset ((∀ i, G i) → ℂ)) (a : S → ℂ)
        (ℓ : S → ∀ i, SmoothDual (ρ i)) (w : S → ∀ i, V i),
        ∀ g, H (r j) g = ∑ k : S, a k * ∏ i,
          matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ k i)) (w k i) (g i) := by
    apply exists_finite_productCoefficient_expansion ρ hρ hcof
      ⟨H (r j), Submodule.subset_span ?_⟩
    exact ⟨L (r j), ⟨v (r j), FiniteTensor.isSmooth_external ρ (fun i => (hρ i).1) _⟩, rfl⟩
  choose S a ℓ w hsamples using hsamples
  let J := Σ j : Fin q, S j
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J,
    fun j => a (e.symm j).1 (e.symm j).2 • φ (e.symm j).1,
    fun j => ℓ (e.symm j).1 (e.symm j).2,
    fun j => w (e.symm j).1 (e.symm j).2, ?_⟩
  intro x g
  change H x g = _
  calc
    H x g = ∑ j : Fin q, φ j x * H (r j) g := hr g x
    _ = ∑ j : Fin q, ∑ k : S j, (a j k * φ j x) * ∏ i,
        matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ j k i)) (w j k i) (g i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hsamples j g, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ z : J, (a z.1 z.2 * φ z.1 x) * ∏ i,
        matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ z.1 z.2 i))
          (w z.1 z.2 i) (g i) := (Fintype.sum_sigma (fun z : J => (a z.1 z.2 * φ z.1 x) * ∏ i,
        matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ z.1 z.2 i))
          (w z.1 z.2 i) (g i))).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun z => by dsimp only; rw [e.symm_apply_apply]; rfl)

end CompactFamily

section Padic

open MeasureTheory

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The compact two-section pairing before integration over the compact group. -/
def compactProductPairingKernel
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((smoothContragredient (B.blockTensor σ)).comp (B.leviProjection F.Carrier))) →
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) →
      GeneralLinear n F.Carrier → GeneralLinear n F.Carrier → B.Levi F.Carrier → ℂ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  exact fun h f k k' m => smoothDualPairing (B.blockTensor σ)
    (Induction.eval _ _ h k) (B.blockTensor σ m (Induction.eval _ _ f k'))

/-- The actual compact-section pairing has one finite expansion, uniform in
both compact arguments and the Levi element, into actual block coefficients. -/
theorem exists_compactProductPairing_expansion
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI := T.leviTopologicalGroup B
    (∀ i, IsAdmissible (σ i)) →
      ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (K : Set (GeneralLinear n F.Carrier)) →
        ∀ (h : Induction.SmoothFunctions (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B)
              ((smoothContragredient (B.blockTensor σ)).comp (B.leviProjection F.Carrier))))
          (f : Induction.SmoothFunctions (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B)
              ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))),
          ∃ (N : ℕ) (φ : Fin N → HarmonicAnalysis.SchwartzBruhat (K × K))
            (ℓ : Fin N → ∀ i, SmoothDual (σ i)) (w : Fin N → ∀ i, V i),
            ∀ (k k' : K) (m : B.Levi F.Carrier),
              compactProductPairingKernel T B σ h f k k' m =
                ∑ j : Fin N, φ j (k, k') * ∏ i,
                  matrixCoefficient (σ i) (smoothDualPairing (σ i) (ℓ j i))
                    (w j i) (m i) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let : ∀ i : Fin B.length, IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  intro hσ K hK h f
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcof : ∀ i (H : OpenSubgroup (GeneralLinear (B.size i) F.Carrier)),
      ∃ L : OpenSubgroup (GeneralLinear (B.size i) F.Carrier),
        IsCompact (L : Set (GeneralLinear (B.size i) F.Carrier)) ∧ L ≤ H := by
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
    ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
      IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
      (∀ g : GeneralLinear n F.Carrier,
        ∃ (q : B.parabolic F.Carrier) (k : K),
          g = (q : GeneralLinear n F.Carrier) * (k : GeneralLinear n F.Carrier)) ∧
      (letI : MeasurableSpace K := borel K
       ∃ μ : Measure K, μ.IsHaarMeasure ∧ IsProbabilityMeasure μ ∧
         ∀ (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)),
           (∀ i, IsAdmissible (σ i)) →
           ∃ E : Representation.Equiv
               (smoothContragredient (T.normalizedProductInduced B σ))
               (T.normalizedParabolicInduced B (smoothContragredient (B.blockTensor σ))),
             ∀ (ℓ : SmoothDual (T.normalizedProductInduced B σ))
               (f : Induction.SmoothFunctions (B.parabolic F.Carrier)
                 (twist (T.parabolicHalfModulus B)
                   ((B.blockTensor σ).comp (B.leviProjection F.Carrier))))
               (g : GeneralLinear n F.Carrier),
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

end Langlands.GodementJacquet
