import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof
import Langlands.AllField.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof
import Langlands.AllField.Representation.RankinSelberg.RankOneTestReduction
import Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedRankOneStatement
/-!
# Highly ramified L-vanishing against a representation of `GL_1`, every local field

Proof of `WhittakerTypeHighlyRamifiedRankOneLVanishingStatement` (JPSS 1983,
Proposition 2.13 with `r = 0`). The finite-function asymptotic argument gives one
conductor bound before every quasicharacter and test function. Since the smaller
member of the pair has rank one, only the first power of the twisting character
occurs in the torus integrals, and a character of large conductor is nontrivial on
the needed principal-unit group in every characteristic. Laurentness forces the
normalized common denominator to be one, preserving its full measure certificate.
-/

noncomputable section


namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RamifiedFiniteFunctionMellinStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement WhittakerTypeHighlyRamifiedLVanishingStatement ZeroRowLastRowCutoffStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_determinantOrder continuous_ord_units determinantCharacter_rootCoordinates determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue exists_equalRankCompactRootExpansion_twist exists_equalRankRootExpansion_twist exists_equalRank_ramified_laurent exists_highlyRamified_ordered_pair_of_analytic_inputs exists_highlyRamified_symmetric_of_analytic_inputs exists_highlyRamified_symmetric_of_ordered exists_isPadicPairLPolynomial_quasicharacter_twist exists_unequalRankZeroRowCompactRootExpansion_twist exists_unequalRankZeroRowRootExpansion_twist exists_unequalRankZeroRow_ramified_laurent exists_uniform_ramified_finiteFamily_integrals exists_uniform_ramified_root_integrals exists_uniform_ramified_tensor_integrals finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicPairLPolynomial_twist_left_iff_right isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration ramifiedFiniteFunctionMellin rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus whittakerTypeHighlyRamifiedLVanishing whittakerTypeHighlyRamifiedLVanishing_of_analytic_inputs zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement PrincipalUnitPowerCofinalityStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists principalUnitPowerCofinality
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV uW

/-- Scalar ramified Mellin certificates and the conductor give one threshold
for a fixed finite tensor family whose coordinate exponents are all `1`. -/
theorem exists_uniform_ramified_tensor_integrals_unitExponent
    {F : Type uF} [Field F] (T : LocalFieldData F) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    let dμ := localMultiplicativeHaar F
    let scalar := fun (η : Fˣ → ℂ) (α : Quasicharacter F)
        (m : ℕ) (φ : SchwartzBruhat F) (s : ℂ) (a : Fˣ) =>
      φ (a : F) * η a * (α a : ℂ) *
        (T.normalizedAbs (a : F) : ℂ) ^ ((m : ℂ) * s)
    ∀ {J : Type*} [Fintype J] (r : ℕ) (m : Fin r → ℕ),
      (∀ i, m i = 1) →
      ∀ (η : J → Fin r → Fˣ → ℂ) (cη : J → ℂ),
      (∀ j i, ∃ b : ℕ, ∀ α : Quasicharacter F,
        (∃ u ∈ T.principalUnits b, α u ≠ 1) →
        ∀ φ : SchwartzBruhat F,
          (∃ c : ℝ, ∀ s : ℂ, c < s.re →
            Integrable (scalar (η j i) α (m i) φ s) dμ) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, scalar (η j i) α (m i) φ s a ∂dμ)
              (laurentToRatFunc L)) →
      ∃ A : ℕ, ∀ χ : Quasicharacter F,
        A ≤ T.multiplicativeConductor χ →
        ∀ (K : ℕ) (cΦ : Fin K → ℂ)
          (φ : Fin K → Fin r → SchwartzBruhat F),
        let f := fun (s : ℂ) (a : Fin r → Fˣ) =>
          (∑ k, cΦ k * ∏ i, φ k i (a i : F)) *
          (∑ j, cη j * ∏ i, η j i (a i)) *
          ∏ i, (χ (a i) : ℂ) ^ (m i) *
            (T.normalizedAbs (a i : F) : ℂ) ^ ((m i : ℂ) * s)
        (∃ c : ℝ, ∀ s : ℂ, c < s.re →
          Integrable (f s) (Measure.pi fun _ : Fin r => dμ)) ∧
        ∃ L : LaurentCoefficients,
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, f s a ∂Measure.pi fun _ : Fin r => dμ)
            (laurentToRatFunc L) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : SecondCountableTopology Fˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  dsimp only
  intro J _ r m hm η cη hscalar
  choose b hb using hscalar
  have hB : ∀ j i, ∀ χ : Quasicharacter F,
      b j i + 1 ≤ T.multiplicativeConductor χ →
        ∃ v : Fˣ, v ∈ T.principalUnits (b j i) ∧ (χ v) ^ (m i) ≠ 1 := by
    intro j i χ hχ
    obtain ⟨v, hv, hχv⟩ :=
      T.exists_nontrivial_below_multiplicativeConductor χ (b j i) (by omega)
    exact ⟨v, hv, by rwa [hm i, pow_one]⟩
  obtain ⟨A, hA⟩ :=
    (Set.finite_range (fun ji : J × Fin r => b ji.1 ji.2 + 1)).bddAbove
  refine ⟨A, fun χ hχ K cΦ φ => ?_⟩
  apply laurentContinuation_tensor_integral
    (fun _ : Fin r => localMultiplicativeHaar F)
    cη cΦ η (fun k i a => φ k i (a : F))
    (fun i s a => (χ a : ℂ) ^ (m i) *
      (T.normalizedAbs (a : F) : ℂ) ^ ((m i : ℂ) * s))
  intro k j i
  obtain ⟨u, hu, hne⟩ := hB j i χ
    ((hA (Set.mem_range_self (j, i))).trans hχ)
  have hnontrivial : ∃ u ∈ T.principalUnits (b j i), (χ ^ m i) u ≠ 1 :=
    ⟨u, hu, by simpa only [ContinuousMonoidHom.pow_apply] using hne⟩
  simpa only [ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val, mul_assoc]
    using hb j i (χ ^ m i) hnontrivial (φ k i)

/-- The published finite-function tensor, scalar ramified Mellin and power
theorems give a threshold for a fixed finite torus family and every test
that has a Schwartz tensor expansion. -/
theorem exists_uniform_ramified_finiteFamily_integrals_unitExponent
    {F : Type uF} [Field F] (T : LocalFieldData F) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    let dμ := localMultiplicativeHaar F
    ∀ (r : ℕ) (m : Fin r → ℕ), (∀ i, m i = 1) →
    (∀ Φ : SchwartzBruhat (Fin r → F),
      ∃ (K : ℕ) (c : Fin K → ℂ)
        (φ : Fin K → Fin r → SchwartzBruhat F),
        ∀ x, Φ x = ∑ k, c k * ∏ i, φ k i (x i)) →
    ∀ {ι : Type*} [Fintype ι] (η : ι → (Fin r → Fˣ) → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fin r → Fˣ =>
            fun a : Fin r → Fˣ => η j (b * a)))) →
    ∃ A : ℕ, ∀ χ : Quasicharacter F,
      A ≤ T.multiplicativeConductor χ →
      ∀ j (Φ : SchwartzBruhat (Fin r → F)),
        let f := fun (s : ℂ) (a : Fin r → Fˣ) =>
          Φ (fun i => (a i : F)) * η j a *
            ∏ i, (χ (a i) : ℂ) ^ (m i) *
              (T.normalizedAbs (a i : F) : ℂ) ^ ((m i : ℂ) * s)
        (∃ c : ℝ, ∀ s : ℂ, c < s.re →
          Integrable (f s) (Measure.pi fun _ : Fin r => dμ)) ∧
        ∃ L : LaurentCoefficients,
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, f s a ∂Measure.pi fun _ : Fin r => dμ)
            (laurentToRatFunc L) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  dsimp only
  intro r m hm hSchwartz ι _ η hη
  have heach (j : ι) :
      ∃ A : ℕ, ∀ χ : Quasicharacter F,
        A ≤ T.multiplicativeConductor χ →
        ∀ Φ : SchwartzBruhat (Fin r → F),
          let f := fun (s : ℂ) (a : Fin r → Fˣ) =>
            Φ (fun i => (a i : F)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (m i) *
                (T.normalizedAbs (a i : F) : ℂ) ^ ((m i : ℂ) * s)
          (∃ c : ℝ, ∀ s : ℂ, c < s.re →
            Integrable (f s)
              (Measure.pi fun _ : Fin r => localMultiplicativeHaar F)) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, f s a
                ∂Measure.pi fun _ : Fin r => localMultiplicativeHaar F)
              (laurentToRatFunc L) := by
    obtain ⟨N, cη, fη, hfη, hηexp⟩ :=
      finiteFunctionTensor Fˣ r (η j) (hη j)
    have hsc := fun k i =>
      ramifiedFiniteFunctionMellin F T (fη k i) (hfη k i)
    choose b hb using hsc
    obtain ⟨A, hA⟩ := exists_uniform_ramified_tensor_integrals_unitExponent T r m hm fη cη
      (fun k i => ⟨b k i, fun α hα φ =>
        hb k i α hα (m i) (by rw [hm i]; exact Nat.one_pos) φ⟩)
    refine ⟨A, fun χ hχ Φ => ?_⟩
    obtain ⟨K, cΦ, φ, hΦ⟩ := hSchwartz Φ
    simpa only [hΦ, hηexp] using hA χ hχ K cΦ φ
  choose B hB using heach
  obtain ⟨A, hA⟩ := (Set.finite_range B).bddAbove
  exact ⟨A, fun χ hχ j Φ =>
    hB j χ ((hA (Set.mem_range_self j)).trans hχ) Φ⟩

/-- The published scalar and tensor theorems give the root-weight torus
certificates of the one-coordinate torus (`n = 0`, exponent `1`), with one
threshold before every quasicharacter and test. -/
theorem exists_uniform_ramified_root_integrals_rankOne
    {F : Type uF} [Field F] (T : LocalFieldData F) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    let dμ := localMultiplicativeHaar F
    ∀ n : ℕ, n = 0 →
    ∀ (N : ℕ) (η : Fin N → (Fin (n + 1) → Fˣ) → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fin (n + 1) → Fˣ =>
            fun a : Fin (n + 1) → Fˣ => η j (b * a)))) →
    ∃ B : ℕ, ∀ χ : Quasicharacter F,
      B ≤ T.multiplicativeConductor χ →
      ∀ j (Φ : SchwartzBruhat (Fin (n + 1) → F)),
        let f := fun (s : ℂ) (a : Fin (n + 1) → Fˣ) =>
          Φ (fun i => (a i : F)) * η j a *
            ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
              (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
        (∃ c : ℝ, ∀ s : ℂ, c < s.re →
          Integrable (f s) (Measure.pi fun _ : Fin (n + 1) => dμ)) ∧
        ∃ L : LaurentCoefficients,
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, f s a ∂Measure.pi fun _ : Fin (n + 1) => dμ)
            (laurentToRatFunc L) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  dsimp only
  intro n hn N η hη
  subst hn
  simpa only [Nat.cast_add, Nat.cast_one] using
    exists_uniform_ramified_finiteFamily_integrals_unitExponent T
      (0 + 1) (fun i => i.val + 1) (fun i => by have := i.isLt; omega)
      (rowTensorDecomposition F (0 + 1)) η hη

section PadicWhittakerType

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Existing symmetric factor existence supplies an ordered certificate for
any continuous determinant twist when the first rank is at least the second. -/
theorem exists_isPadicPairLPolynomial_quasicharacter_twist [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (hex : SymmetricLPolynomialExistenceStatement.{uF, uV, uW})
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {r : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hnr : n ≤ r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (χ : Quasicharacter F) :
    ∃ P : ℂ[X], IsPadicPairLPolynomial F ψ ν.val
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ P := by
  obtain ⟨P, hP⟩ := hex F ψ ν r n V W
    (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ
    ((isOfWhittakerType_quasicharacter_twist_iff (⟨⟩ : LocalFieldData F) ψ χ π).mpr hπ) hσ
  exact ⟨P, (isPadicSymmetricLPolynomial_of_le hnr).mp hP⟩

/-- Root coordinates give precisely the positive powers of the twisting
character, including powers divisible by the residue characteristic. -/
theorem determinantCharacter_rootCoordinates (T : LocalFieldData F)
    (χ : Fˣ →* ℂˣ) (a : Fin (n + 1) → Fˣ)
    (k : Langlands.GeneralLinear (n + 1) F) :
    (χ.comp determinant)
      (Iwasawa.diagonalUnits (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * k) =
        (∏ i : Fin (n + 1), χ (a i) ^ (i.val + 1)) * χ (determinant k) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hdet : determinant
      (Iwasawa.diagonalUnits (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j)) =
      ∏ i : Fin (n + 1), a i ^ (i.val + 1) := by
    apply Units.ext
    change Matrix.det (Iwasawa.diagonalUnits
      (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j)).val = _
    simpa only [Units.coe_prod, Units.val_pow_eq_pow_val] using
      (((rootCoordinateChange F T n).2.2.2.2.2.2 a).2.2.1)
  change χ (determinant (_ * k)) = _
  rw [map_mul, hdet, map_mul, map_prod]
  simp only [map_pow]

end PadicWhittakerType

/-- The untwisted coefficient expansions fix the finite family before every
determinant twist. The character of the right translate is absorbed in the
Schwartz coefficients; the exact positive coordinate powers remain explicit. -/
theorem exists_equalRankRootExpansion_twist
    {F : Type uF} [Field F] (T : LocalFieldData F)
    (n : ℕ) :
    letI := T.topology
    let A := Fin (n + 1) → Fˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
      (ψ : UnitaryAdditiveCharacter F),
      CoefficientTorusExpansion (standardCharacter ψ n) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : Fˣ →* ℂˣ)
        (f : WhittakerFunctions ψ n),
        f ∈ whittakerSet ψ n (Langlands.twist (χ.comp determinant) π) →
      ∀ (f' : InverseWhittakerFunctions ψ n),
        f' ∈ inverseWhittakerSet ψ n σ →
      ∀ (Φ : SchwartzBruhat (Fin (n + 1) → F))
        (k : Langlands.GeneralLinear (n + 1) F),
      ∃ Ψ : Fin N → SchwartzBruhat (Fin (n + 1) → F),
        ∀ a : A,
          let g := Iwasawa.diagonalUnits (d a) * k
          f.val g * f'.val g * Φ (lastRow g) * w a =
            ∑ j, Ψ j (fun i => (a i : F)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) := by
  classical
  let := T.topology
  dsimp only
  intro V _ _ W _ _ π σ ψ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ := equalRankRootExpansion F T n V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ f hf f' hf' Φ k
  obtain ⟨f₀, ⟨ℓ₀, hf₀⟩, htw⟩ := (mem_whittakerSet_twist_iff ψ χ).mp hf
  obtain ⟨ℓ', hf'⟩ := hf'
  obtain ⟨Ψ, hΨ⟩ := hexp ℓ₀ ℓ' ⟨f₀, hf₀⟩ ⟨f', hf'⟩ Φ k
  refine ⟨fun j => (χ (determinant k) : ℂ) • Ψ j, ?_⟩
  intro a
  have hχ :
      (χ (determinant
        (Iwasawa.diagonalUnits
          (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * k)) : ℂ) =
      (∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) * (χ (determinant k) : ℂ) := by
    simpa only [MonoidHom.comp_apply, Units.val_mul, Units.coe_prod,
      Units.val_pow_eq_pow_val] using
      congrArg Units.val (determinantCharacter_rootCoordinates T χ a k)
  rw [htw, hχ]
  calc
    _ = ((∑ j, Ψ j (fun i => (a i : F)) * η j a) *
        (χ (determinant k) : ℂ)) *
          ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) := by
      rw [← hΨ a]
      ring
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      change (Ψ j (fun i => (a i : F)) * η j a *
          (χ (determinant k) : ℂ)) *
            (∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) =
        ((χ (determinant k) : ℂ) * Ψ j (fun i => (a i : F))) *
          η j a * (∏ i, (χ (a i) : ℂ) ^ (i.val + 1))
      ring

/-- The actual normalized compact average for every determinant twist uses
the same finite family fixed by the untwisted coefficient expansions. -/
theorem exists_equalRankCompactRootExpansion_twist
    {F : Type uF} [Field F] (T : LocalFieldData F)
    (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
    let κ := (generalLinearHaar F n).restrict (K : Set _)
    let A := Fin (n + 1) → Fˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
      (ψ : UnitaryAdditiveCharacter F),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ n) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : Quasicharacter F)
        (ℓ : glFunctionals ψ n
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π))
        (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      ∃ (r : ℕ) (c : Fin r → ℝ)
        (Ψ : Fin r → Fin N → SchwartzBruhat (Fin (n + 1) → F)),
        (∀ t, 0 ≤ c t) ∧ (∑ t, c t) = 1 ∧
        ∀ (a : A) (s : ℂ),
          let H := fun z : Langlands.GeneralLinear (n + 1) F =>
            equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
              (Iwasawa.diagonalUnits (d a) * z) * w a
          let S := fun t : Fin r =>
            ∑ j, Ψ t j (fun i => (a i : F)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
                (T.normalizedAbs (a i : F) : ℂ) ^
                  ((i.val + 1 : ℂ) * s)
          Integrable H κ ∧
          (∫ z, H z ∂κ) = ∑ t, (c t : ℂ) * S t ∧
          (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let A := Fin (n + 1) → Fˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let v : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  dsimp only
  intro V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_equalRankRootExpansion_twist T n V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ ℓ ℓ' f f' Φ
  have hsχ : IsSmooth
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (Langlands.AllField.RankinSelberg.quasicharacter_isOpen_ker T χ))).mpr hsπ
  obtain ⟨r, k, c, hc, hmass, havg⟩ :=
    equalRankNormalizedCompactIntegration F T n V W _ σ hsχ hsσ ψ ℓ ℓ' f f' Φ
  choose Ψ hΨ using fun t : Fin r =>
    hexp χ f.val ⟨ℓ, f.property⟩ f'.val ⟨ℓ', f'.property⟩ Φ (k t).val
  refine ⟨r, c, Ψ, hc, hmass, ?_⟩
  intro a s
  let H₀ := fun z : Langlands.GeneralLinear (n + 1) F =>
    equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
      (Iwasawa.diagonalUnits (d a) * z)
  let S := fun t : Fin r =>
    ∑ j, Ψ t j (fun i => (a i : F)) * η j a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  have hpoint (t : Fin r) : H₀ (k t).val * w a = S t := by
    have hdet := ((rootSpectralWeight F T n).2 a (k t).val
      ((rootSpectralWeight F T n).1 (k t)) s).1
    change (f.val.val _ * f'.val.val _ * Φ (lastRow _) *
      determinantWeight (normalizedAbsoluteValue T) _ s) * w a = S t
    rw [hdet]
    change (f.val.val _ * f'.val.val _ * Φ (lastRow _) * v a s) * w a = S t
    calc
      _ = (f.val.val _ * f'.val.val _ * Φ (lastRow _) * w a) * v a s := by ring
      _ = (∑ j, Ψ t j (fun i => (a i : F)) * η j a *
          ∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) * v a s :=
        congrArg (fun z : ℂ => z * v a s) (hΨ t a)
      _ = S t := by
        simp only [Finset.sum_mul, Finset.prod_mul_distrib, S, v, mul_assoc]
  obtain ⟨hi, hsum, habs⟩ := havg (Iwasawa.diagonalUnits (d a)) s
  change Integrable (fun z => H₀ z * w a) κ ∧
    (∫ z, H₀ z * w a ∂κ) = ∑ t, (c t : ℂ) * S t ∧
    (∫⁻ z, ‖H₀ z * w a‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ
  refine ⟨hi.mul_const (w a), ?_, ?_⟩
  · rw [integral_mul_const, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, hpoint]
  · calc
      (∫⁻ z, ‖H₀ z * w a‖ₑ ∂κ) = (∫⁻ z, ‖H₀ z‖ₑ ∂κ) * ‖w a‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_mul_const' _ _ enorm_ne_top
      _ = (∑ t, ENNReal.ofReal (c t) * ‖H₀ (k t).val‖ₑ) * ‖w a‖ₑ := by rw [habs]
      _ = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_assoc, ← enorm_mul, hpoint]

/-- Uniform Laurent certificates for fixed finite torus families transfer to
every actual equal-rank zeta value, at every compatible quotient measure.
The torus and Iwasawa inputs remain explicit analytic hypotheses. -/
theorem exists_equalRank_ramified_laurent
    {F : Type uF} [Field F] (T : LocalFieldData F)
    (n : ℕ) (hI : QuotientIwasawaIntegrationStatement F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    let A := Fin (n + 1) → Fˣ
    let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
    let I := fun (χ : Quasicharacter F) (η : A → ℂ)
        (Ψ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) (a : A) =>
      Ψ (fun i => (a i : F)) * η a *
        ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
          (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
    (∀ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) →
      ∃ B : ℕ, ∀ χ : Quasicharacter F,
        B ≤ T.multiplicativeConductor χ →
        ∀ j (Ψ : SchwartzBruhat (Fin (n + 1) → F)),
          (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I χ (η j) Ψ s) dA) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, I χ (η j) Ψ s a ∂dA) (laurentToRatFunc L)) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
      (ψ : UnitaryAdditiveCharacter F),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ n) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ B : ℕ, ∀ χ : Quasicharacter F,
      B ≤ T.multiplicativeConductor χ →
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F),
        QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F)
          (generalLinearHaar F n) (unipotentHaar F n) μ →
        ∀ R ∈ equalRankZetaValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ
            (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ,
          ∃ L : LaurentCoefficients, laurentToRatFunc L = R := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let A := Fin (n + 1) → Fˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let I := fun (χ : Quasicharacter F) (η : A → ℂ)
      (Ψ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) (a : A) =>
    Ψ (fun i => (a i : F)) * η a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  dsimp only
  intro htorus V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_equalRankCompactRootExpansion_twist T n V W π σ ψ hsπ hsσ hπ hσ
  obtain ⟨B, hB⟩ := htorus N η hη
  refine ⟨B, fun χ hχ hright μ hμ R hR => ?_⟩
  rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, Φ, _hconv, hR⟩
  let fm : (coefficientModel
    (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule := ⟨f, hf⟩
  let fm' : (coefficientModel σ ℓ').toSubmodule := ⟨f', hf'⟩
  obtain ⟨r, c, Ψ, _hc, _hmass, hformula⟩ := hexp χ ℓ ℓ' fm fm' Φ
  let H := fun (s : ℂ) (a : A) (z : Langlands.GeneralLinear (n + 1) F) =>
    equalRankFunction ψ (normalizedAbsoluteValue T) f f' Φ s
      (Iwasawa.diagonalUnits (d a) * z) * w a
  let S := fun (t : Fin r) (s : ℂ) (a : A) => ∑ j, I χ (η j) (Ψ t j) s a
  have hsum (s : ℂ) (a : A) :
      (∫ z, H s a z ∂κ) = ∑ t, (c t : ℂ) * S t s a :=
    (hformula a s).2.1
  have habs (s : ℂ) (a : A) :
      (∫⁻ z, ‖H s a z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t s a‖ₑ :=
    (hformula a s).2.2
  have hSdata (t : Fin r) :
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (S t s) dA) ∧
      ∃ L : LaurentCoefficients,
        HasRationalContinuation T.residueCardinality
          (fun s => ∫ a, S t s a ∂dA) (laurentToRatFunc L) := by
    simpa only [one_mul] using
      laurentContinuation_sum_integral dA (fun _ : Fin N => (1 : ℂ))
        (fun j => I χ (η j) (Ψ t j)) (fun j => hB χ hχ j (Ψ t j))
  have htotal := laurentContinuation_sum_integral dA
    (fun t => (c t : ℂ)) S hSdata
  choose b hb using fun t => (hSdata t).1
  obtain ⟨b₀, hb₀⟩ := (Set.finite_range b).bddAbove
  have hS (s : ℂ) (hs : b₀ < s.re) (t : Fin r) : Integrable (S t s) dA :=
    hb t s ((hb₀ (Set.mem_range_self t)).trans_lt hs)
  have hnorm (s : ℂ) (hs : b₀ < s.re) :
      (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤ := by
    simp_rw [habs]
    rw [lintegral_finsetSum' Finset.univ
      (f := fun t a => ENNReal.ofReal (c t) * ‖S t s a‖ₑ)
      (fun t _ => aemeasurable_const.mul (hS s hs t).aestronglyMeasurable.enorm)]
    apply ENNReal.sum_lt_top.mpr
    intro t _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp (hS s hs t).hasFiniteIntegral)
  have hsχ : IsSmooth
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (Langlands.AllField.RankinSelberg.quasicharacter_isOpen_ker T χ))).mpr hsπ
  have hmeas (s : ℂ) :
      Measurable (equalRankIntegrand ψ (normalizedAbsoluteValue T) f f' Φ s) :=
    (equalRankIntegrandContinuous F n (normalizedAbsoluteValue T)
      (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
      V W _ σ hsχ hsσ ψ ℓ ℓ' fm fm' Φ s).measurable
  have htransport (s : ℂ) :
      (EqualRankConverges ψ (normalizedAbsoluteValue T) μ f f' Φ s ↔
        (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      (EqualRankConverges ψ (normalizedAbsoluteValue T) μ f f' Φ s →
        equalRankIntegral ψ (normalizedAbsoluteValue T) μ f f' Φ s =
          ∫ a, ∫ z, H s a z ∂κ ∂dA) :=
    (quotientRootIntegration F T n hI μ hμ).2
      (equalRankIntegrand ψ (normalizedAbsoluteValue T) f f' Φ s) (hmeas s)
  obtain ⟨L, hL⟩ := htotal.2
  have hLactual : HasRationalContinuation T.residueCardinality
      (equalRankIntegral ψ (normalizedAbsoluteValue T) μ f f' Φ) (laurentToRatFunc L) := by
    apply RationalContinuationLinear.continuation_of_eq_on_right hL
    refine ⟨b₀, fun s hs => ?_⟩
    rw [(htransport s).2 ((htransport s).1.mpr (hnorm s hs))]
    simp_rw [hsum]
  exact ⟨L, hLactual.unique T.residueCardinality_gt_one hR⟩

/-- The published zero-row root expansion fixes the same finite family before
every twist. The larger block has precisely the smaller determinant. -/
theorem exists_unequalRankZeroRowRootExpansion_twist
    {F : Type uF} [Field F] (T : LocalFieldData F)
    (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    let A := Fin (n + 1) → Fˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ
        (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
      (ψ : UnitaryAdditiveCharacter F),
      CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : Fˣ →* ℂˣ)
        (f : WhittakerFunctions ψ (n + (0 + k + 1))),
        f ∈ whittakerSet ψ (n + (0 + k + 1))
          (Langlands.twist (χ.comp determinant) π) →
      ∀ (f' : InverseWhittakerFunctions ψ n),
        f' ∈ inverseWhittakerSet ψ n σ →
      ∀ z : K,
      ∃ Ψ : Fin N → SchwartzBruhat (Fin (n + 1) → F),
        ∀ (a : A) (s : ℂ),
          unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f f' s 0
              (Iwasawa.diagonalUnits (d a) * z.val) * w a =
            ∑ j, Ψ j (fun i => (a i : F)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
                (T.normalizedAbs (a i : F) : ℂ) ^
                  ((i.val + 1 : ℂ) * s) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  dsimp only
  intro V _ _ W _ _ π σ ψ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    unequalRankZeroRowRootExpansion F T n k V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ f hf f' hf' z
  obtain ⟨f₀, ⟨ℓ₀, hf₀⟩, htw⟩ := (mem_whittakerSet_twist_iff ψ χ).mp hf
  obtain ⟨ℓ', hf'⟩ := hf'
  obtain ⟨Ψ, hΨ⟩ := hexp ℓ₀ ℓ' ⟨f₀, hf₀⟩ ⟨f', hf'⟩ z
  refine ⟨fun j => (χ (determinant z.val) : ℂ) • Ψ j, ?_⟩
  intro a s
  have hχ :
      (χ (determinant
        (Iwasawa.diagonalUnits
          (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * z.val)) : ℂ) =
      (∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) * (χ (determinant z.val) : ℂ) := by
    simpa only [MonoidHom.comp_apply, Units.val_mul, Units.coe_prod,
      Units.val_pow_eq_pow_val] using
      congrArg Units.val (determinantCharacter_rootCoordinates T χ a z.val)
  have htwfun (g : Langlands.GeneralLinear (n + 1) F) :
      unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f f' s 0 g =
        (χ (determinant g) : ℂ) *
          unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f₀ f' s 0 g := by
    simp only [unequalRankFunction, htw, determinant_unequalRankMatrix]
    ring
  rw [htwfun, hχ]
  calc
    _ = (χ (determinant z.val) : ℂ) *
        (unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f₀ f' s 0
          (Iwasawa.diagonalUnits
            (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * z.val) *
            (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
              ((i.val + 1) * (n - i.val)))⁻¹) *
          ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) := by ring
    _ = _ := by
      rw [hΨ a s]
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib]
      apply Finset.sum_congr rfl
      intro j _
      change _ = ((χ (determinant z.val) : ℂ) *
        Ψ j (fun i => (a i : F))) * η j a * _
      ring

/-- The published zero-row compact integration theorem gives exact ordinary
and absolute averages for twists, with the untwisted root family unchanged. -/
theorem exists_unequalRankZeroRowCompactRootExpansion_twist
    {F : Type uF} [Field F] (T : LocalFieldData F)
    (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
    let κ := (generalLinearHaar F n).restrict (K : Set _)
    let A := Fin (n + 1) → Fˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ
        (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
      (ψ : UnitaryAdditiveCharacter F),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : Quasicharacter F)
        (ℓ : glFunctionals ψ (n + (0 + k + 1))
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π))
        (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ (r : ℕ) (c : Fin r → ℝ)
        (Ψ : Fin r → Fin N → SchwartzBruhat (Fin (n + 1) → F)),
        (∀ t, 0 ≤ c t) ∧ (∑ t, c t) = 1 ∧
        ∀ (a : A) (s : ℂ),
          let H := fun z : Langlands.GeneralLinear (n + 1) F =>
            unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
              (Iwasawa.diagonalUnits (d a) * z) * w a
          let S := fun t : Fin r =>
            ∑ j, Ψ t j (fun i => (a i : F)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
                (T.normalizedAbs (a i : F) : ℂ) ^
                  ((i.val + 1 : ℂ) * s)
          Integrable H κ ∧
          (∫ z, H z ∂κ) = ∑ t, (c t : ℂ) * S t ∧
          (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let A := Fin (n + 1) → Fˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  dsimp only
  intro V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_unequalRankZeroRowRootExpansion_twist T n k V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ ℓ ℓ' f f'
  have hsχ : IsSmooth
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (Langlands.AllField.RankinSelberg.quasicharacter_isOpen_ker T χ))).mpr hsπ
  obtain ⟨r, z, c, hc, hmass, havg⟩ :=
    unequalRankZeroRowNormalizedCompactIntegration F T n k V W _ σ hsχ hsσ ψ ℓ ℓ' f f'
  choose Ψ hΨ using fun t : Fin r =>
    hexp χ f.val ⟨ℓ, f.property⟩ f'.val ⟨ℓ', f'.property⟩ (z t)
  refine ⟨r, c, Ψ, hc, hmass, ?_⟩
  intro a s
  let H₀ := fun u : Langlands.GeneralLinear (n + 1) F =>
    unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
      (Iwasawa.diagonalUnits (d a) * u)
  let S := fun t : Fin r =>
    ∑ j, Ψ t j (fun i => (a i : F)) * η j a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  have hpoint (t : Fin r) : H₀ (z t).val * w a = S t := hΨ t a s
  obtain ⟨hi, hsum, habs⟩ := havg (Iwasawa.diagonalUnits (d a)) s
  change Integrable (fun u => H₀ u * w a) κ ∧
    (∫ u, H₀ u * w a ∂κ) = ∑ t, (c t : ℂ) * S t ∧
    (∫⁻ u, ‖H₀ u * w a‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ
  refine ⟨hi.mul_const (w a), ?_, ?_⟩
  · rw [integral_mul_const, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, hpoint]
  · calc
      (∫⁻ u, ‖H₀ u * w a‖ₑ ∂κ) = (∫⁻ u, ‖H₀ u‖ₑ ∂κ) * ‖w a‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_mul_const' _ _ enorm_ne_top
      _ = (∑ t, ENNReal.ofReal (c t) * ‖H₀ (z t).val‖ₑ) * ‖w a‖ₑ := by rw [habs]
      _ = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_assoc, ← enorm_mul, hpoint]

/-- Uniform Laurent certificates for fixed finite torus families transfer to
every actual zero-row unequal-rank zeta value, at every compatible quotient measure.
The torus and Iwasawa inputs remain explicit analytic hypotheses. -/
theorem exists_unequalRankZeroRow_ramified_laurent
    {F : Type uF} [Field F] (T : LocalFieldData F)
    (n k : ℕ) (hI : QuotientIwasawaIntegrationStatement F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    let A := Fin (n + 1) → Fˣ
    let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
    let I := fun (χ : Quasicharacter F) (η : A → ℂ)
        (Ψ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) (a : A) =>
      Ψ (fun i => (a i : F)) * η a *
        ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
          (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
    (∀ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) →
      ∃ B : ℕ, ∀ χ : Quasicharacter F,
        B ≤ T.multiplicativeConductor χ →
        ∀ j (Ψ : SchwartzBruhat (Fin (n + 1) → F)),
          (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I χ (η j) Ψ s) dA) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, I χ (η j) Ψ s a ∂dA) (laurentToRatFunc L)) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ
        (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
      (ψ : UnitaryAdditiveCharacter F),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ B : ℕ, ∀ χ : Quasicharacter F,
      B ≤ T.multiplicativeConductor χ →
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F),
        QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F)
          (generalLinearHaar F n) (unipotentHaar F n) μ →
        ∀ (ν : AdditiveHaarMeasure F),
        ∀ R ∈ unequalRankZetaValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) 0 k μ (rectangularMeasure ν 0 (n + 1))
            (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ,
          ∃ L : LaurentCoefficients, laurentToRatFunc L = R := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let A := Fin (n + 1) → Fˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let I := fun (χ : Quasicharacter F) (η : A → ℂ)
      (Ψ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) (a : A) =>
    Ψ (fun i => (a i : F)) * η a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  dsimp only
  intro htorus V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_unequalRankZeroRowCompactRootExpansion_twist T n k
      V W π σ ψ hsπ hsσ hπ hσ
  obtain ⟨B, hB⟩ := htorus N η hη
  refine ⟨B, fun χ hχ hright μ hμ ν R hR => ?_⟩
  rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, _hconv, hR⟩
  let fm : (coefficientModel
    (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule := ⟨f, hf⟩
  let fm' : (coefficientModel σ ℓ').toSubmodule := ⟨f', hf'⟩
  obtain ⟨r, c, Ψ, _hc, _hmass, hformula⟩ := hexp χ ℓ ℓ' fm fm'
  let H := fun (s : ℂ) (a : A) (z : Langlands.GeneralLinear (n + 1) F) =>
    unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f f' s 0
      (Iwasawa.diagonalUnits (d a) * z) * w a
  let S := fun (t : Fin r) (s : ℂ) (a : A) => ∑ j, I χ (η j) (Ψ t j) s a
  have hsum (s : ℂ) (a : A) :
      (∫ z, H s a z ∂κ) = ∑ t, (c t : ℂ) * S t s a :=
    (hformula a s).2.1
  have habs (s : ℂ) (a : A) :
      (∫⁻ z, ‖H s a z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t s a‖ₑ :=
    (hformula a s).2.2
  have hSdata (t : Fin r) :
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (S t s) dA) ∧
      ∃ L : LaurentCoefficients,
        HasRationalContinuation T.residueCardinality
          (fun s => ∫ a, S t s a ∂dA) (laurentToRatFunc L) := by
    simpa only [one_mul] using
      laurentContinuation_sum_integral dA (fun _ : Fin N => (1 : ℂ))
        (fun j => I χ (η j) (Ψ t j)) (fun j => hB χ hχ j (Ψ t j))
  have htotal := laurentContinuation_sum_integral dA
    (fun t => (c t : ℂ)) S hSdata
  choose b hb using fun t => (hSdata t).1
  obtain ⟨b₀, hb₀⟩ := (Set.finite_range b).bddAbove
  have hS (s : ℂ) (hs : b₀ < s.re) (t : Fin r) : Integrable (S t s) dA :=
    hb t s ((hb₀ (Set.mem_range_self t)).trans_lt hs)
  have hnorm (s : ℂ) (hs : b₀ < s.re) :
      (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤ := by
    simp_rw [habs]
    rw [lintegral_finsetSum' Finset.univ
      (f := fun t a => ENNReal.ofReal (c t) * ‖S t s a‖ₑ)
      (fun t _ => aemeasurable_const.mul (hS s hs t).aestronglyMeasurable.enorm)]
    apply ENNReal.sum_lt_top.mpr
    intro t _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp (hS s hs t).hasFiniteIntegral)
  have hsχ : IsSmooth
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (Langlands.AllField.RankinSelberg.quasicharacter_isOpen_ker T χ))).mpr hsπ
  have hmeas (s : ℂ) :
      Measurable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) :=
    (unequalRankZeroRowIntegrandContinuous F n k (normalizedAbsoluteValue T)
      (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
      V W _ σ hsχ hsσ ψ ℓ ℓ' fm fm' s).measurable
  have htransport (s : ℂ) :
      (Integrable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) μ ↔
        (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      (Integrable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) μ →
        (∫ q, unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0 q ∂μ) =
          ∫ a, ∫ z, H s a z ∂κ ∂dA) :=
    (quotientRootIntegration F T n hI μ hμ).2
      (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) (hmeas s)
  obtain ⟨L, hL⟩ := htotal.2
  have hLactual : HasRationalContinuation T.residueCardinality
      (unequalRankIntegral ψ (normalizedAbsoluteValue T) 0 k μ
        (rectangularMeasure ν 0 (n + 1)) f f') (laurentToRatFunc L) := by
    apply RationalContinuationLinear.continuation_of_eq_on_right hL
    refine ⟨b₀, fun s hs => ?_⟩
    simp only [unequalRankIntegral, rectangularMeasure_zero_rows, integral_dirac]
    rw [(htransport s).2 ((htransport s).1.mpr (hnorm s hs))]
    simp_rw [hsum]
  exact ⟨L, hLactual.unique T.residueCardinality_gt_one hR⟩

section Pair


end Pair

section PadicTwist

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {ψ : UnitaryAdditiveCharacter F}
  {ν : letI := borel F
    AdditiveHaarMeasure F}
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {P : ℂ[X]}

/-- The equal-rank family at one compatible measure likewise determines
the polynomial in the full p-adic pair certificate. -/
theorem IsPadicPairLPolynomial.eq_one_of_laurent_equalRank
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hL :
      letI := borel F
      letI : BorelSpace F := ⟨rfl⟩
      letI := borel (Langlands.GeneralLinear (n + 1) F)
      letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
      letI := borel (upperUnipotent (n + 1) F)
      letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient n F)
      ∃ _ : Measure.IsMulRightInvariant (unipotentHaar F n),
        ∃ μ : Measure (LeftUnipotentQuotient n F),
          QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F)
            (generalLinearHaar F n) (unipotentHaar F n) μ ∧
          ∀ R ∈ equalRankZetaValues (⟨⟩ : LocalFieldData F).residueCardinality ψ
              (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ π σ,
            ∃ L : LaurentCoefficients, laurentToRatFunc L = R) : P = 1 := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  obtain ⟨h, μ, hμ, hL⟩ := hL
  let := h
  exact (hP.2 μ hμ).eq_one_of_laurent_equalRank hL

/-- Moving a determinant twist preserves the entire compatible-measure
certificate, including its existence clause. -/
theorem isPadicPairLPolynomial_twist_left_iff_right
    (χ : Fˣ →* ℂˣ) :
    IsPadicPairLPolynomial F ψ ν (Langlands.twist (χ.comp determinant) π) σ P ↔
      IsPadicPairLPolynomial F ψ ν π (Langlands.twist (χ.comp determinant) σ) P := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  exact imp_congr_right fun _ => isPairLPolynomial_twist_left_iff_right χ

/-- Larger-first vanishing in the two possible orientations suffices for
the symmetric relation, with the twist on the original first member. -/
theorem exists_highlyRamified_symmetric_of_ordered
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hlarge : n ≤ r → ∃ A : ℕ,
      ∀ χ : (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ →
        IsPadicPairLPolynomial F ψ ν
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ 1)
    (hsmall : r < n → ∃ A : ℕ,
      ∀ χ : (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ →
        IsPadicPairLPolynomial F ψ ν
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) σ) π 1) :
    ∃ A : ℕ,
      ∀ χ : (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ 1 := by
  by_cases hnr : n ≤ r
  · obtain ⟨A, hA⟩ := hlarge hnr
    exact ⟨A, fun χ hχ => (isPadicSymmetricLPolynomial_of_le hnr).mpr (hA χ hχ)⟩
  · have hrn : r < n := Nat.lt_of_not_ge hnr
    obtain ⟨A, hA⟩ := hsmall hrn
    refine ⟨A, fun χ hχ => (isPadicSymmetricLPolynomial_of_lt hrn).mpr ?_⟩
    exact (isPadicPairLPolynomial_twist_left_iff_right
      (π := σ) (σ := π) (χ : Fˣ →* ℂˣ)).mp (hA χ hχ)

end PadicTwist

/-- Quotient Iwasawa integration, coefficient expansions and common factor
existence imply ordered-pair vanishing when the smaller member is a
representation of `GL_1` (`n = 0`), using the published scalar and tensor
proofs. The witness measure comes from the common certificate. -/
theorem exists_highlyRamified_ordered_pair_of_analytic_inputs_rankOne
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (n : ℕ) (hn : n = 0)
    (hI : QuotientIwasawaIntegrationStatement F (⟨⟩ : LocalFieldData F) n) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    ∀ (r : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      n ≤ r →
      IsOfWhittakerType r (standardCharacter ψ r) π →
      IsOfWhittakerType n (standardCharacter ψ n) σ →
      CoefficientTorusExpansion (standardCharacter ψ r) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
      (∀ χ : Quasicharacter F, ∃ P : ℂ[X],
        IsPadicPairLPolynomial F ψ ν.val
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ P) →
    ∃ A : ℕ, ∀ χ : Quasicharacter F,
      A ≤ T.multiplicativeConductor χ →
        IsPadicPairLPolynomial F ψ ν.val
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ 1 := by
  classical
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  dsimp only
  intro r V _ _ W _ _ π σ hnr hπ hσ heπ heσ hex
  have htorus := exists_uniform_ramified_root_integrals_rankOne T n hn
  by_cases heq : r = n
  · subst r
    obtain ⟨A, hA⟩ := exists_equalRank_ramified_laurent T n hI htorus
      V W π σ ψ hπ.1.1 hσ.1.1 heπ heσ
    refine ⟨A, fun χ hχ => ?_⟩
    obtain ⟨P, hP⟩ := hex χ
    have hPone : P = 1 := hP.eq_one_of_laurent_equalRank (by
      obtain ⟨h, μ, hμ⟩ := hP.1
      let := h
      exact ⟨h, μ, hμ, hA χ hχ μ hμ⟩)
    exact hPone ▸ hP
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = n + (0 + k + 1) :=
      ⟨r - n - 1, by omega⟩
    obtain ⟨A, hA⟩ := exists_unequalRankZeroRow_ramified_laurent T n k hI
      htorus V W π σ ψ hπ.1.1 hσ.1.1 heπ heσ
    refine ⟨A, fun χ hχ => ?_⟩
    obtain ⟨P, hP⟩ := hex χ
    have hPone : P = 1 := by
      obtain ⟨h, μ, hμ⟩ := hP.1
      let := h
      have hgen := (isPairLPolynomial_of_lt (by omega : n < n + (0 + k + 1))).mp
        (hP.2 μ hμ) 0 k rfl
      exact normalizedGenerator_eq_one_of_laurent hgen (hA χ hχ μ hμ ν.val)
    exact hPone ▸ hP

/-- The analytic inputs in both orientations imply symmetric vanishing when
the twisted member is a representation of `GL_1`. In both orientations the
smaller member has rank one. Symmetric factor existence is used only in the
original carrier universes; in the smaller-first branch its twist is moved to
the larger member. -/
theorem exists_highlyRamified_symmetric_of_analytic_inputs_rankOne
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (hex : SymmetricLPolynomialExistenceStatement.{uF,uV,uW})
    (hI : ∀ n, QuotientIwasawaIntegrationStatement F (⟨⟩ : LocalFieldData F) n) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    ∀ (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsOfWhittakerType 0 (standardCharacter ψ 0) π →
      IsOfWhittakerType n (standardCharacter ψ n) σ →
      CoefficientTorusExpansion (standardCharacter ψ 0) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ 0) π →
      CoefficientTorusExpansion (standardCharacter ψ n) σ →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ A : ℕ, ∀ χ : Quasicharacter F,
      A ≤ T.multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν.val
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ 1 := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  dsimp only
  intro n V _ _ W _ _ π σ hπ hσ heπ heπInv heσ heσInv
  apply exists_highlyRamified_symmetric_of_ordered π σ
  · intro hnr
    refine exists_highlyRamified_ordered_pair_of_analytic_inputs_rankOne ψ ν n
      (by omega) (hI n) 0 π σ hnr
      hπ hσ heπ heσInv ?_
    intro χ
    exact exists_isPadicPairLPolynomial_quasicharacter_twist
      hex ψ ν π σ hnr hπ hσ χ
  · intro hrn
    refine exists_highlyRamified_ordered_pair_of_analytic_inputs_rankOne ψ ν 0
      rfl (hI 0) n σ π
      (Nat.le_of_lt hrn) hσ hπ heσ heπInv ?_
    intro χ
    obtain ⟨P, hP⟩ := hex F ψ ν 0 n V W
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ
      ((isOfWhittakerType_quasicharacter_twist_iff T ψ χ π).mpr hπ) hσ
    refine ⟨P, ?_⟩
    exact (isPadicPairLPolynomial_twist_left_iff_right
      (π := σ) (σ := π) (χ : Fˣ →* ℂˣ)).mpr
        ((isPadicSymmetricLPolynomial_of_lt hrn).mp hP)

/-- Symmetric polynomial existence implies the rank-one target, using the
published full-torus expansion and normalized quotient Iwasawa integration.
The expansion proof is instantiated at the independent carrier universes. -/
theorem whittakerTypeHighlyRamifiedRankOneLVanishing_of_analytic_inputs
    (hex : SymmetricLPolynomialExistenceStatement.{uF,uV,uW}) :
    WhittakerTypeHighlyRamifiedRankOneLVanishingStatement.{uF,uV,uW} := by
  intro F _ _ _ _ ψ ν n V _ _ W _ _ π σ hπ hσ
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hπInv := (isOfWhittakerType_standard_iff_inverse ψ π).mp hπ
  have hσInv := (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  exact exists_highlyRamified_symmetric_of_analytic_inputs_rankOne ψ ν hex
    (fun n => quotientIwasawaIntegration F T n) n π σ hπ hσ
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uV}
      F T 0 V π ψ _ (Or.inl rfl) hπ)
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uV}
      F T 0 V π ψ _ (Or.inr rfl) hπInv)
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uW}
      F T n W σ ψ _ (Or.inl rfl) hσ)
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uW}
      F T n W σ ψ _ (Or.inr rfl) hσInv)

/-- JPSS Proposition 2.13 for a first member of rank one, over every
nonarchimedean local field: sufficiently ramified determinant twists have
symmetric L-polynomial one, with a uniform natural conductor bound and the
full compatible-measure certificate. -/
theorem whittakerTypeHighlyRamifiedRankOneLVanishing :
    WhittakerTypeHighlyRamifiedRankOneLVanishingStatement.{uF,uV,uW} :=
  whittakerTypeHighlyRamifiedRankOneLVanishing_of_analytic_inputs
    symmetricLPolynomialExists.{uF,uV,uW}

end Langlands.AllField.RankinSelberg
