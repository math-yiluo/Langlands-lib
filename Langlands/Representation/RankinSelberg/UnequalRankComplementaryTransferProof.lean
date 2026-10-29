import Langlands.Representation.RankinSelberg.UnequalRankComplementaryTransferStatement
import Langlands.Representation.RankinSelberg.UnequalRankFourierSmearingProof
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.UnequalRankBlockIntegrationProof
import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportProof
import Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationProof
import Langlands.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.HarmonicAnalysis.PadicRowFourierCutoffProof
import Langlands.HarmonicAnalysis.RowFourierMeasure
import Langlands.Group.GL.RankReindex
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.MeasureTheory.Group.Integral

/-! Paired complementary-block transfer using one original-model coefficient.
Published support, coefficient integration, Fourier smearing, conjugation and
normalized cutoff results give both inner rectangular identities. These lift
to the actual iterated quotient integrals without a quotient-variable
interchange. Both real half-plane bounds can be chosen as zero. -/

noncomputable section

namespace Langlands.RankinSelberg.ComplementaryTransfer

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uX uW

section FourierSign

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] {d : ℕ}

omit [BorelSpace F] in
/-- An even output makes the same supplied Fourier pair valid for the inverse
character, without a change of Haar measure or scalar normalization. -/
theorem fourierPair_inverse_of_even (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F) (Φ κ : SchwartzBruhat (Fin d → F))
    (hpair : IsRowFourierPair ψ ν Φ κ) (heven : ∀ x, κ (-x) = κ x) :
    IsRowFourierPair (ψ.scale (-1)) ν Φ κ := by
  intro y
  change κ y = rowFourierIntegralWithMeasure (ψ.scale (-1)) (rowMeasure ν d) Φ y
  rw [rowFourierIntegralWithMeasure_scale_neg_one_eq]
  exact (heven y).symm.trans (hpair (-y))

end FourierSign

section SmallStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {X : Type uX} [TopologicalSpace X]

/-- The preimage of an open subgroup fixing one model coefficient is a
neighborhood on which all its right translates have the same value.
No topology is placed on the representation carrier. -/
theorem exists_open_coefficient_invariance
    (π : Representation ℂ G V) (hπ : IsSmooth π)
    {N : Subgroup G} {θ : N →* ℂˣ} (ℓ : functionals N θ π)
    (U : X → G) (hU : Continuous U) (x₀ : X) (hU₀ : U x₀ = 1)
    (f : (coefficientModel π ℓ).toSubmodule) :
    ∃ O : Set X, IsOpen O ∧ x₀ ∈ O ∧
      ∀ x ∈ O, ∀ h : G, f.val.val (h * U x) = f.val.val h := by
  obtain ⟨K, hK⟩ := model_isSmooth π hπ ℓ f
  refine ⟨U ⁻¹' (K : Set G), K.isOpen.preimage hU, ?_, ?_⟩
  · change U x₀ ∈ K
    rw [hU₀]
    exact K.one_mem
  · intro x hx h
    exact congrArg (fun e : (coefficientModel π ℓ).toSubmodule => e.val.val h)
      (hK ⟨U x, hx⟩)

end SmallStabilizer

section ReflectedPlateau

variable {X : Type uX} [AddCommGroup X] [MeasurableSpace X] [MeasurableNeg X]

/-- An even plateau removes the minus sign in the lower-row average.
The weighted integral's genuine integrability also gives that of the
unweighted lower-row function. -/
theorem reflected_plateau_integral (μ : Measure X) [Measure.IsNegInvariant μ]
    (Φ H : X → ℂ) (C : Set X)
    (hC : ∀ x, H x ≠ 0 → x ∈ C)
    (hplateau : ∀ x ∈ C, Φ x = 1) (heven : ∀ x, Φ (-x) = Φ x)
    (hi : Integrable (fun x => Φ x * H (-x)) μ) :
    Integrable H μ ∧
      (∫ x, Φ x * H (-x) ∂μ) = ∫ x, H x ∂μ := by
  have he (x : X) : Φ x * H (-x) = H (-x) := by
    by_cases hx : H (-x) = 0
    · simp only [hx, mul_zero]
    · rw [← heven x, hplateau (-x) (hC (-x) hx), one_mul]
  simp_rw [he] at hi ⊢
  exact ⟨by simpa only [neg_neg] using hi.comp_neg, integral_neg_eq_self H μ⟩

end ReflectedPlateau

section NormalizedCutoff

variable {X : Type uX} [MeasurableSpace X]

/-- A mass-one cutoff supported where a row coefficient is constant has exactly
that constant as its integral. Its genuine integrability comes from the cutoff.
This is the scalar step used after the complementary stabilizer calculation. -/
theorem normalized_cutoff_integral (μ : Measure X) (κ H : X → ℂ) (c : ℂ)
    (hi : Integrable κ μ) (hmass : (∫ x, κ x ∂μ) = 1)
    (hfix : ∀ x, κ x ≠ 0 → H x = c) :
    Integrable (fun x => κ x * H x) μ ∧
      (∫ x, κ x * H x ∂μ) = c := by
  have he (x : X) : κ x * H x = κ x * c := by
    by_cases hx : κ x = 0
    · simp only [hx, zero_mul]
    · rw [hfix x hx]
  simp_rw [he]
  exact ⟨hi.mul_const c, by rw [integral_mul_const, hmass, one_mul]⟩

end NormalizedCutoff

section IteratedAssembly

variable {X : Type uX} [AddCommGroup X] [MeasurableSpace X] [MeasurableNeg X]
  {Y : Type*} [MeasurableSpace Y] {Z : Type*} [MeasurableSpace Z]

/-- Scalar original-block assembly after the actual rectangular Fubini and
matrix identities have been supplied. Its reflected row average is the one
constructed by pulling back the complementary dual smear. The splitting
identity is an explicit premise of this scalar lemma. -/
theorem lower_average_integral_transfer
    (μ : Measure X) [Measure.IsNegInvariant μ] (ν : Measure Y) (ρ : Measure Z)
    (H : Y → X → ℂ) (A : Y → ℂ) (B : Z → ℂ) (Φ : X → ℂ) (C : Set X)
    (hC : ∀ y x, H y x ≠ 0 → x ∈ C)
    (hplateau : ∀ x ∈ C, Φ x = 1) (heven : ∀ x, Φ (-x) = Φ x)
    (haverage : ∀ y, Integrable (fun x => Φ x * H y (-x)) μ ∧
      A y = ∫ x, Φ x * H y (-x) ∂μ)
    (hsplit : (∫ z, B z ∂ρ) = ∫ y, ∫ x, H y x ∂μ ∂ν) :
    (∀ y, Integrable (H y) μ) ∧ (∫ z, B z ∂ρ) = ∫ y, A y ∂ν := by
  have hrow (y : Y) : Integrable (H y) μ ∧ A y = ∫ x, H y x ∂μ := by
    have hp := reflected_plateau_integral μ Φ (H y) C (hC y)
      hplateau heven (haverage y).1
    exact ⟨hp.1, (haverage y).2.trans hp.2⟩
  refine ⟨fun y => (hrow y).1, ?_⟩
  rw [hsplit]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (hrow y).2.symm

omit [AddCommGroup X] [MeasurableNeg X] in
/-- Scalar complementary-block assembly after genuine rectangular splitting.
The same normalized small cutoff multiplies the original dual coefficient;
invariance wherever that cutoff is nonzero removes the new last row. -/
theorem dual_cutoff_integral_transfer
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    (H : Y → X → ℂ) (A : Y → ℂ) (B : Z → ℂ) (κ : X → ℂ)
    (hi : Integrable κ μ) (hmass : (∫ x, κ x ∂μ) = 1)
    (hfix : ∀ y x, κ x ≠ 0 → H y x = A y)
    (hsplit : (∫ z, B z ∂ρ) = ∫ y, ∫ x, κ x * H y x ∂μ ∂ν) :
    (∀ y, Integrable (fun x => κ x * H y x) μ) ∧
      (∫ z, B z ∂ρ) = ∫ y, A y ∂ν := by
  have hrow (y : Y) := normalized_cutoff_integral μ κ (H y) (A y) hi hmass
    (hfix y)
  refine ⟨fun y => (hrow y).1, ?_⟩
  rw [hsplit]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (hrow y).2

end IteratedAssembly

section RectangularAssembly

open AdjacentBlockReduction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

set_option backward.isDefEq.respectTransparency false in
/-- The concrete original rectangular transfer. The full rectangular
integrability premise permits the published last-row Fubini theorem; the
global reflected lower average is evaluated at the neighboring block matrix. -/
theorem original_rectangular_transfer (n j k : ℕ)
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure]
    [Measure.IsNegInvariant (rowMeasure ν (n + 1))]
    (ψ : UnitaryAdditiveCharacter F)
    (f f₀ : WhittakerFunctions ψ (n + ((j + 1) + k + 1)))
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (C : Set (Fin (n + 1) → F))
    (hC : ∀ g X, f.val (unequalRankMatrix (j + 1) k g X) ≠ 0 →
      X (Fin.last j) ∈ C)
    (hplateau : ∀ x ∈ C, Φ x = 1) (heven : ∀ x, Φ (-x) = Φ x)
    (hfull : ∀ g, Integrable
      (fun X => f.val (unequalRankMatrix (j + 1) k g X))
      (rectangularMeasure ν (j + 1) (n + 1)))
    (haverage : ∀ h,
      Integrable (fun x => Φ x * f.val
        (h * rectangularUnipotent (j + 1) k (Fin.snoc 0 (-x))))
        (rowMeasure ν (n + 1)) ∧
      f₀.val h = ∫ x, Φ x * f.val
        (h * rectangularUnipotent (j + 1) k (Fin.snoc 0 (-x)))
        ∂rowMeasure ν (n + 1)) :
    ∀ g,
      (∫ X, f.val (unequalRankMatrix (j + 1) k g X)
        ∂rectangularMeasure ν (j + 1) (n + 1)) =
      ∫ Y, f₀.val (blockMatrixAt j (k + 1) (by omega) g Y)
        ∂rectangularMeasure ν j (n + 1) := by
  intro g
  rw [rectangular_integral_lastRow ν j (n + 1) _ (hfull g)]
  apply integral_congr_ae
  filter_upwards [] with Y
  have hbase : unequalRankMatrix (j + 1) k g (Fin.snoc Y 0) =
      blockMatrixAt j (k + 1) (by omega) g Y :=
    blockMatrixAt_snoc_zero j k rfl (by omega) g Y
  have ha := haverage (blockMatrixAt j (k + 1) (by omega) g Y)
  rw [← hbase] at ha
  simp_rw [← unequalRankMatrix_snoc] at ha
  have hs : ∀ x, f.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y x)) ≠ 0 →
      x ∈ C := by
    intro x hx
    simpa only [Fin.snoc_last] using hC g (Fin.snoc Y x) hx
  have hp := reflected_plateau_integral (rowMeasure ν (n + 1)) Φ
    (fun x => f.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y x)))
    C hs hplateau heven ha.1
  simpa only [hbase] using (ha.2.trans hp.2).symm

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalRing F] [BorelSpace F] in
/-- The concrete complementary rectangular transfer. The cutoff identity and
full rectangular integrability refer to the same actual coefficient. A
mass-one cutoff inside the original coefficient's stabilizer removes the row. -/
theorem cutoff_rectangular_transfer (n j k : ℕ)
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure]
    (ψ : UnitaryAdditiveCharacter F)
    (f f₀ : WhittakerFunctions ψ (n + ((j + 1) + k + 1)))
    (κ : SchwartzBruhat (Fin (n + 1) → F))
    (hi : Integrable κ (rowMeasure ν (n + 1)))
    (hmass : (∫ x, κ x ∂rowMeasure ν (n + 1)) = 1)
    (hfix : ∀ x, κ x ≠ 0 → ∀ h,
      f.val (h * rectangularUnipotent (j + 1) k (Fin.snoc 0 x)) = f.val h)
    (hcut : ∀ g X,
      f₀.val (unequalRankMatrix (j + 1) k g X) =
        κ (X (Fin.last j)) * f.val (unequalRankMatrix (j + 1) k g X))
    (hfull : ∀ g, Integrable
      (fun X => f₀.val (unequalRankMatrix (j + 1) k g X))
      (rectangularMeasure ν (j + 1) (n + 1))) :
    ∀ g,
      (∫ X, f₀.val (unequalRankMatrix (j + 1) k g X)
        ∂rectangularMeasure ν (j + 1) (n + 1)) =
      ∫ Y, f.val (blockMatrixAt j (k + 1) (by omega) g Y)
        ∂rectangularMeasure ν j (n + 1) := by
  intro g
  rw [rectangular_integral_lastRow ν j (n + 1) _ (hfull g)]
  apply integral_congr_ae
  filter_upwards [] with Y
  have hbase : unequalRankMatrix (j + 1) k g (Fin.snoc Y 0) =
      blockMatrixAt j (k + 1) (by omega) g Y :=
    blockMatrixAt_snoc_zero j k rfl (by omega) g Y
  simp_rw [hcut, Fin.snoc_last]
  apply (normalized_cutoff_integral (rowMeasure ν (n + 1)) κ
    (fun x => f.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y x)))
    (f.val (blockMatrixAt j (k + 1) (by omega) g Y)) hi hmass ?_).2
  intro x hx
  rw [unequalRankMatrix_snoc, hfix x hx, hbase]

end RectangularAssembly

section RankTransport

open AdjacentBlockReduction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

/-- Original rectangular transfer in a fixed large group. -/
theorem original_rectangular_transferAt (n r j k : ℕ)
    (hr : r = n + ((j + 1) + k + 1))
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure]
    [Measure.IsNegInvariant (rowMeasure ν (n + 1))]
    (ψ : UnitaryAdditiveCharacter F) (f f₀ : WhittakerFunctions ψ r)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (C : Set (Fin (n + 1) → F))
    (hC : ∀ g X, f.val (blockMatrixAt (j + 1) k hr g X) ≠ 0 →
      X (Fin.last j) ∈ C)
    (hplateau : ∀ x ∈ C, Φ x = 1) (heven : ∀ x, Φ (-x) = Φ x)
    (hfull : ∀ g, Integrable
      (fun X => f.val (blockMatrixAt (j + 1) k hr g X))
      (rectangularMeasure ν (j + 1) (n + 1)))
    (haverage : ∀ h,
      Integrable (fun x => Φ x * f.val
        (h * GeneralLinear.reindex (finCongr (by omega))
          (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-x)))))
        (rowMeasure ν (n + 1)) ∧
      f₀.val h = ∫ x, Φ x * f.val
        (h * GeneralLinear.reindex (finCongr (by omega))
          (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-x))))
        ∂rowMeasure ν (n + 1)) :
    ∀ g,
      (∫ X, f.val (blockMatrixAt (j + 1) k hr g X)
        ∂rectangularMeasure ν (j + 1) (n + 1)) =
      ∫ Y, f₀.val (blockMatrixAt j (k + 1) (by omega) g Y)
        ∂rectangularMeasure ν j (n + 1) := by
  subst r
  simp only [reindex_finCongr_rfl, MulEquiv.refl_apply] at haverage
  exact original_rectangular_transfer n j k ν ψ f f₀ Φ C hC hplateau heven
    hfull haverage

omit [IsTopologicalRing F] [BorelSpace F] in
/-- Complementary rectangular transfer in a fixed large group. -/
theorem cutoff_rectangular_transferAt (n r j k : ℕ)
    (hr : r = n + ((j + 1) + k + 1))
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure]
    (ψ : UnitaryAdditiveCharacter F) (f f₀ : WhittakerFunctions ψ r)
    (κ : SchwartzBruhat (Fin (n + 1) → F))
    (hi : Integrable κ (rowMeasure ν (n + 1)))
    (hmass : (∫ x, κ x ∂rowMeasure ν (n + 1)) = 1)
    (hfix : ∀ x, κ x ≠ 0 → ∀ h,
      f.val (h * GeneralLinear.reindex (finCongr (by omega))
        (rectangularUnipotent (j + 1) k (Fin.snoc 0 x))) = f.val h)
    (hcut : ∀ g X,
      f₀.val (blockMatrixAt (j + 1) k hr g X) =
        κ (X (Fin.last j)) * f.val (blockMatrixAt (j + 1) k hr g X))
    (hfull : ∀ g, Integrable
      (fun X => f₀.val (blockMatrixAt (j + 1) k hr g X))
      (rectangularMeasure ν (j + 1) (n + 1))) :
    ∀ g,
      (∫ X, f₀.val (blockMatrixAt (j + 1) k hr g X)
        ∂rectangularMeasure ν (j + 1) (n + 1)) =
      ∫ Y, f.val (blockMatrixAt j (k + 1) (by omega) g Y)
        ∂rectangularMeasure ν j (n + 1) := by
  subst r
  simp only [reindex_finCongr_rfl, MulEquiv.refl_apply] at hfix
  exact cutoff_rectangular_transfer n j k ν ψ f f₀ κ hi hmass hfix hcut hfull

omit [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F] in
/-- The published complementary conjugation at an arbitrary equal large rank. -/
theorem complementary_conjugationAt (n r j k : ℕ)
    (hr : r = n + ((j + 1) + k + 1)) (hnr : n < r)
    (z : Fin (n + 1) → F) :
    inverseTranspose (r + 1) F
      ((blockWeylAt n r hnr)⁻¹ *
        GeneralLinear.reindex (finCongr (by omega))
          (unequalRankSmearingUnipotent n k j z) *
        blockWeylAt n r hnr) =
      GeneralLinear.reindex (finCongr (by omega))
        (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-z))) := by
  subst r
  simpa only [reindex_finCongr_rfl, MulEquiv.refl_apply] using
    (unequalRankComplementaryConjugation.{uF,0}.1 F n j k z)

end RankTransport

section UniformIntegrability

open AdjacentBlockReduction

/-- The published uniform support theorem and the published coefficient
integration theorem discharge full rectangular integrability for the actual
supplied scalar Haar measure, before any quotient integral is considered. -/
theorem exists_uniform_support_integrable
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n r j k : ℕ) (hr : r = n + (j + k + 1)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V,
      IsOfWhittakerType r (standardCharacter ψ r) π →
    ∀ (ℓ : glFunctionals ψ r π), ℓ.val ≠ 0 →
    ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier),
        IsCompact C ∧
        (∀ g X, f.val.val (blockMatrixAt j k hr g X) ≠ 0 → X ∈ C) ∧
        ∀ g, Integrable (fun X => f.val.val (blockMatrixAt j k hr g X))
          (rectangularMeasure ν j (n + 1)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : SigmaCompactSpace F.Carrier := T.sigmaCompactSpace
  let : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : BorelSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier) :=
    inferInstanceAs (BorelSpace (Fin j → Fin (n + 1) → F.Carrier))
  subst r
  intro ψ ν V _ _ π hπ ℓ hℓ f
  obtain ⟨C, hC, hs⟩ := unequalRankCompactSupport.{uF,uV} F T n j k ψ V π hπ ℓ hℓ f
  refine ⟨C, hC, hs, ?_⟩
  exact blockCoefficient_integrable ν n j k ψ π hπ.1.1 ℓ f C hC hs

end UniformIntegrability

section ActualIntegrals

open AdjacentBlockReduction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]

omit [IsTopologicalRing F] in
/-- Equal rectangular coefficient integrals at every smaller-group argument
give equal actual quotient integrals for every spectral parameter. Only the
rectangular identities are premises; no interchange with the quotient variable
is used. The equal-rank transports retain the original coefficient space. -/
theorem unequalRankIntegralAt_congr_inner
    (j k j' k' : ℕ) (hr : r = n + (j + k + 1))
    (hr' : r = n + (j' + k' + 1))
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (ν' : Measure (Matrix (Fin j') (Fin (n + 1)) F))
    (f f₀ : WhittakerFunctions ψ r) (f' : InverseWhittakerFunctions ψ n)
    (hinner : ∀ g : Langlands.GeneralLinear (n + 1) F,
      (∫ x, f.val (blockMatrixAt j k hr g x) ∂ν) =
        ∫ x, f₀.val (blockMatrixAt j' k' hr' g x) ∂ν') :
    ∀ s : ℂ,
      unequalRankIntegralAt j k hr ψ abv μ ν f f' s =
        unequalRankIntegralAt j' k' hr' ψ abv μ ν' f₀ f' s := by
  intro s
  rw [unequalRankIntegralAt_eq_outer, unequalRankIntegralAt_eq_outer]
  have hgap : j + k + 1 = j' + k' + 1 := by omega
  simp_rw [hinner, hgap]

end ActualIntegrals

section DualAverage

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {r : ℕ} {X : Type uX} [MeasurableSpace X]

/-- Pull a global upper-column average back through the literal translated dual
function. The final assembly supplies the matrix-conjugation premise using
the published complementary conjugation theorem. -/
theorem dual_average_pullback (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure X) (w : X → ℂ)
    (a : Langlands.GeneralLinear (r + 1) F)
    (U L : X → Langlands.GeneralLinear (r + 1) F)
    (hUL : ∀ x, inverseTranspose (r + 1) F (a⁻¹ * U x * a) = L x)
    (f f₀ : WhittakerFunctions ψ r)
    (hglobal : ∀ q : Langlands.GeneralLinear (r + 1) F,
      Integrable (fun x => w x *
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f) a).val
          (q * U x)) μ ∧
      (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f₀) a).val q =
        ∫ x, w x *
          (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f) a).val
            (q * U x) ∂μ) :
    ∀ h : Langlands.GeneralLinear (r + 1) F,
      Integrable (fun x => w x * f.val (h * L x)) μ ∧
      f₀.val h = ∫ x, w x * f.val (h * L x) ∂μ := by
  intro h
  let q := inverseTranspose (r + 1) F (weylLong (r + 1) F * h) * a⁻¹
  have hq : weylLong (r + 1) F * inverseTranspose (r + 1) F (q * a) = h := by
    dsimp [q]
    rw [mul_assoc, inv_mul_cancel, mul_one, inverseTranspose_involutive]
    rw [← mul_assoc, weylLong_mul_self, one_mul]
  have he (x : X) :
      (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f) a).val
        (q * U x) = f.val (h * L x) := by
    simp only [translateWhittaker_apply, firstDualFunction_apply]
    have hx : q * U x * a = (q * a) * (a⁻¹ * U x * a) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [hx, map_mul, ← mul_assoc, hq, hUL x]
  have hg := hglobal q
  simp_rw [he] at hg
  simpa only [translateWhittaker_apply, firstDualFunction_apply, hq] using hg

/-- Choosing the inverse image of a dual-model smear supplies one original-model
coefficient and its global lower-row average, including integrability. -/
theorem exists_original_of_dual_average
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F) (μ : Measure X) (w : X → ℂ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r π)
    (a : Langlands.GeneralLinear (r + 1) F)
    (U L : X → Langlands.GeneralLinear (r + 1) F)
    (hUL : ∀ x, inverseTranspose (r + 1) F (a⁻¹ * U x * a) = L x)
    (f : (coefficientModel π ℓ).toSubmodule)
    (g : (coefficientModel (inverseTransposePullback π)
      (firstDualFunctional ψ π ℓ)).toSubmodule)
    (hglobal : ∀ q : Langlands.GeneralLinear (r + 1) F,
      Integrable (fun x => w x *
        (translatedFirstDualModelEquiv ψ π ℓ a f).val.val (q * U x)) μ ∧
      g.val.val q =
        ∫ x, w x *
          (translatedFirstDualModelEquiv ψ π ℓ a f).val.val (q * U x) ∂μ) :
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      translatedFirstDualModelEquiv ψ π ℓ a f₀ = g ∧
      ∀ h : Langlands.GeneralLinear (r + 1) F,
        Integrable (fun x => w x * f.val.val (h * L x)) μ ∧
        f₀.val.val h = ∫ x, w x * f.val.val (h * L x) ∂μ := by
  let D := translatedFirstDualModelEquiv ψ π ℓ a
  let f₀ := D.symm g
  have hf₀ : D f₀ = g := D.apply_symm_apply g
  refine ⟨f₀, hf₀, ?_⟩
  apply dual_average_pullback ψ μ w a U L hUL f.val f₀.val
  intro q
  change Integrable (fun x => w x * (D f).val.val (q * U x)) μ ∧
    (D f₀).val.val q = _
  rw [hf₀]
  exact hglobal q

end DualAverage

section OneWitness

/-- Construct a single original-model witness using the published global and
pointwise Fourier-smearing theorem. The final assembly supplies the actual
matrix-conjugation premise. -/
theorem exists_lower_average_and_dual_cutoff
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ
      (Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F.Carrier) V,
      IsSmooth π →
    ∀ (ℓ : glFunctionals ψ (n + ((k + 1) + j + 1)) π)
      (f : (coefficientModel π ℓ).toSubmodule)
      (Φ κ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      IsRowFourierPair ψ ν Φ κ →
      (∀ x, κ (-x) = κ x) →
    ∀ (a : Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F.Carrier)
      (L : (Fin (n + 1) → F.Carrier) →
        Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F.Carrier),
      (∀ x, inverseTranspose _ F.Carrier
        (a⁻¹ * unequalRankSmearingUnipotent n k j x * a) = L x) →
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      (∀ h : Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F.Carrier,
        Integrable (fun x => Φ x * f.val.val (h * L x)) (rowMeasure ν (n + 1)) ∧
        f₀.val.val h =
          ∫ x, Φ x * f.val.val (h * L x) ∂rowMeasure ν (n + 1)) ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
        (X : Matrix (Fin (k + 1)) (Fin (n + 1)) F.Carrier),
        (translatedFirstDualModelEquiv ψ π ℓ a f₀).val.val
            (unequalRankMatrix (k + 1) j g X) =
          κ (X (Fin.last k)) *
            (translatedFirstDualModelEquiv ψ π ℓ a f).val.val
              (unequalRankMatrix (k + 1) j g X) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν V _ _ π hπ ℓ f Φ κ hpair heven a L hUL
  have hsmear := unequalRankFourierSmearingStatement.{uF,uV} F T n k j
  let D := translatedFirstDualModelEquiv ψ π ℓ a
  have hinv := fourierPair_inverse_of_even ψ ν Φ κ hpair heven
  obtain ⟨g, hg, hcut⟩ := hsmear (ψ.scale (-1)) ν V (inverseTransposePullback π)
    (inverseTransposePullback_isSmooth π hπ) (firstDualFunctional ψ π ℓ) (D f)
    Φ κ hinv
  obtain ⟨f₀, hf₀, havg⟩ := exists_original_of_dual_average ψ
    (rowMeasure ν (n + 1)) Φ π ℓ a (unequalRankSmearingUnipotent n k j)
    L hUL f g hg
  refine ⟨f₀, havg, ?_⟩
  rw [hf₀]
  exact hcut

end OneWitness

section RankTransportWitness

open AdjacentBlockReduction

/-- The single-witness construction at an arbitrary equal large rank. -/
theorem exists_lower_average_and_dual_cutoffAt
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n r j k : ℕ) (hr : r = n + ((k + 1) + j + 1)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V,
      IsSmooth π →
    ∀ (ℓ : glFunctionals ψ r π) (f : (coefficientModel π ℓ).toSubmodule)
      (Φ κ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      IsRowFourierPair ψ ν Φ κ →
      (∀ x, κ (-x) = κ x) →
    ∀ (a : Langlands.GeneralLinear (r + 1) F.Carrier)
      (L : (Fin (n + 1) → F.Carrier) →
        Langlands.GeneralLinear (r + 1) F.Carrier),
      (∀ x, inverseTranspose _ F.Carrier
        (a⁻¹ * GeneralLinear.reindex (finCongr (by omega))
          (unequalRankSmearingUnipotent n k j x) * a) = L x) →
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      (∀ h : Langlands.GeneralLinear (r + 1) F.Carrier,
        Integrable (fun x => Φ x * f.val.val (h * L x)) (rowMeasure ν (n + 1)) ∧
        f₀.val.val h =
          ∫ x, Φ x * f.val.val (h * L x) ∂rowMeasure ν (n + 1)) ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
        (X : Matrix (Fin (k + 1)) (Fin (n + 1)) F.Carrier),
        (translatedFirstDualModelEquiv ψ π ℓ a f₀).val.val
            (blockMatrixAt (k + 1) j hr g X) =
          κ (X (Fin.last k)) *
            (translatedFirstDualModelEquiv ψ π ℓ a f).val.val
              (blockMatrixAt (k + 1) j hr g X) := by
  subst r
  simpa only [reindex_finCongr_rfl, MulEquiv.refl_apply, blockMatrixAt] using
    (exists_lower_average_and_dual_cutoff.{uF,uV} F T n j k)

end RankTransportWitness


section PairedAssembly

open AdjacentBlockReduction

set_option backward.isDefEq.respectTransparency false in
/-- Assemble the paired transfer from a normalized row cutoff proposition.
The final theorem supplies this proposition by its published proof. -/
theorem complementaryTransfer_of_row_cutoff
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n r : ℕ) (hFourier : PadicRowFourierCutoffStatement F T (n + 1)) :
    UnequalRankComplementaryTransferStatement.{uF,uV,uW} F T n r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : SigmaCompactSpace F.Carrier := T.sigmaCompactSpace
  let : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : BorelSpace (Fin (n + 1) → F.Carrier) := inferInstance
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro hnr ψ _ μ _ ν hν V _ _ W _ _ π σ hπ _ ℓ ℓ' hℓ _ j k hr f f'
  let : Measure.IsNegInvariant (rowMeasure ν (n + 1)) :=
    inferInstanceAs (Measure.IsNegInvariant (Measure.pi (fun _ : Fin (n + 1) => ν.measure)))
  have hr₁ : r = n + ((j + 1) + k + 1) := by omega
  have hr₂ : r = n + ((k + 1) + j + 1) := by omega
  obtain ⟨Cfull, hCfull, hs, hfull⟩ := exists_uniform_support_integrable.{uF,uV}
    F T n r (j + 1) k hr₁ ψ ν V π hπ ℓ hℓ f
  let C : Set (Fin (n + 1) → F.Carrier) :=
    (fun X : Matrix (Fin (j + 1)) (Fin (n + 1)) F.Carrier => X (Fin.last j)) '' Cfull
  have hC : IsCompact C := hCfull.image (continuous_apply (Fin.last j))
  let a := blockWeylAt (F := F.Carrier) n r hnr
  let D := translatedFirstDualModelEquiv ψ π ℓ a
  let Ld : (Fin (n + 1) → F.Carrier) → Langlands.GeneralLinear (r + 1) F.Carrier :=
    fun x => GeneralLinear.reindex (finCongr (by omega))
      (rectangularUnipotent (k + 1) j (Fin.snoc 0 x))
  have hLd : Continuous Ld :=
    (continuous_reindex_finCongr (by omega)).comp (continuous_lastRowUnipotent n k j)
  have hLd₀ : Ld 0 = 1 := by
    have hz : (Fin.snoc 0 (0 : Fin (n + 1) → F.Carrier) :
        Matrix (Fin (k + 1)) (Fin (n + 1)) F.Carrier) = 0 := by
      ext b c
      induction b using Fin.lastCases <;> simp [Fin.snoc]
    simp only [Ld, hz, rectangularUnipotent_zero, map_one]
  obtain ⟨O, hO, hO₀, hfix⟩ := exists_open_coefficient_invariance
    (inverseTransposePullback π) (inverseTransposePullback_isSmooth π hπ.1.1)
    (firstDualFunctional ψ π ℓ) Ld hLd 0 hLd₀ (D f)
  obtain ⟨Φ, κ, hpair, hplateau, hsupp, hmass, hevenΦ, hevenκ⟩ :=
    hFourier ψ ν hν C hC O hO hO₀
  let L : (Fin (n + 1) → F.Carrier) → Langlands.GeneralLinear (r + 1) F.Carrier :=
    fun x => GeneralLinear.reindex (finCongr (by omega))
      (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-x)))
  obtain ⟨f₀, havg, hcut⟩ := exists_lower_average_and_dual_cutoffAt.{uF,uV}
    F T n r j k hr₂ ψ ν V π hπ.1.1 ℓ f Φ κ hpair hevenκ a L
    (fun x => complementary_conjugationAt n r j k hr₁ hnr x)
  have horiginal := original_rectangular_transferAt n r j k hr₁ ν ψ
    f.val f₀.val Φ C (fun g X hX => ⟨X, hs g X hX, rfl⟩)
    hplateau hevenΦ hfull havg
  obtain ⟨_, _, _, hfulld⟩ := exists_uniform_support_integrable.{uF,uV}
    F T n r (k + 1) j hr₂ (ψ.scale (-1)) ν V (inverseTransposePullback π)
    (isOfWhittakerType_firstDual ψ π hπ) (firstDualFunctional ψ π ℓ)
    (firstDualFunctional_ne_zero ψ π hℓ) (D f₀)
  have hi : Integrable κ (rowMeasure ν (n + 1)) :=
    κ.continuous.integrable_of_hasCompactSupport κ.hasCompactSupport
  have hdual := cutoff_rectangular_transferAt n r k j hr₂ ν (ψ.scale (-1))
    (D f).val (D f₀).val κ hi hmass
    (fun x hx h => hfix x (hsupp hx) h) hcut hfulld
  refine ⟨f₀, 0, 0, ?_, ?_⟩
  · intro s _
    exact unequalRankIntegralAt_congr_inner (j + 1) k j (k + 1) hr₁ (by omega)
      ψ (normalizedAbsoluteValue T) μ
      (rectangularMeasure ν (j + 1) (n + 1)) (rectangularMeasure ν j (n + 1))
      f.val f₀.val f'.val horiginal s
  · intro s _
    exact (unequalRankIntegralAt_congr_inner (k + 1) j k (j + 1) hr₂ (by omega)
      (ψ.scale (-1)) (normalizedAbsoluteValue T) μ
      (rectangularMeasure ν (k + 1) (n + 1)) (rectangularMeasure ν k (n + 1))
      (D f₀).val (D f).val (secondDualFunction ψ n f'.val) hdual s).symm

end PairedAssembly

end Langlands.RankinSelberg.ComplementaryTransfer

namespace Langlands.RankinSelberg

open HarmonicAnalysis

universe uF uV uW

/-- One coefficient in the original model transfers both actual original and
complementary dual integrals, with the supplied measures and independent
field and representation universes. -/
theorem unequalRankComplementaryTransfer
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n r : ℕ) : UnequalRankComplementaryTransferStatement.{uF,uV,uW} F T n r :=
  ComplementaryTransfer.complementaryTransfer_of_row_cutoff F T n r
    (padicRowFourierCutoff F T (n + 1))

end Langlands.RankinSelberg
