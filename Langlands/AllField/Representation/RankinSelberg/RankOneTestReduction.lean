import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.AllField.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistProof
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement
/-! # Reduction of rank-one tests to the trivial scalar test -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneWhittakerTypeStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus equalRankFactorSwap isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow quasicharacterSmoothCharacter quasicharacter_isOpen_ker rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneWhittakerType twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test unipotentCharacterChangeModulus zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW


/-- A continuous complex character of the scalar group of a supplied p-adic
realization has open kernel. -/
theorem quasicharacter_isOpen_ker {F : Type uF} [Field F]
    (T : LocalFieldData F)
    (χ : letI := T.topology; Quasicharacter F) :
    letI := T.topology
    IsOpen ((χ : Fˣ →* ℂˣ).ker : Set Fˣ) := by
  let := T.topology
  let := T.generalLinearNonarchimedean 1
  let χdet : Langlands.GeneralLinear 1 F →* ℂˣ :=
    (χ : Fˣ →* ℂˣ).comp determinant
  have hopen : IsOpen (χdet.ker : Set (Langlands.GeneralLinear 1 F)) :=
    isOpen_ker_of_continuous_complex_character χdet
      (χ.continuous.comp (T.generalLinearDeterminant 1).continuous)
  convert hopen.preimage (scalarContinuous (R := F) (n := 1)).continuous using 1
  ext x
  change χ x = 1 ↔ χ (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (R := F) (Fin 1) x)) = 1
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]

/-- The same scalar character, packaged with the open kernel needed for actual
smooth normalized induction. -/
def quasicharacterSmoothCharacter {F : Type uF} [Field F]
    (T : LocalFieldData F)
    (χ : letI := T.topology; Quasicharacter F) :
    letI := T.topology
    Induction.SmoothCharacter ℂ Fˣ := by
  let := T.topology
  exact ⟨(χ : Fˣ →* ℂˣ), quasicharacter_isOpen_ker T χ⟩

/-- Continuous determinant twists retain all three parts of full Whittaker
type, on an arbitrary carrier. -/
theorem isOfWhittakerType_quasicharacter_twist_iff {F : Type uF} [Field F]
    (T : LocalFieldData F)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F)
    (χ : letI := T.topology; Quasicharacter F)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    letI := T.topology
    IsOfWhittakerType n (standardCharacter ψ n)
        (twist ((χ : Fˣ →* ℂˣ).comp determinant) π) ↔
      IsOfWhittakerType n (standardCharacter ψ n) π := by
  let := T.topology
  apply isOfWhittakerType_twist_iff
  · exact (quasicharacter_isOpen_ker T χ).preimage
      (T.generalLinearDeterminant (n + 1)).continuous
  · exact determinantCharacter_unipotent _

section LTwist

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : letI := borel F
    AdditiveHaarMeasure F)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (χ : Fˣ →* ℂˣ) (P : ℂ[X])

/-- Opposite determinant twists preserve the quotient-measure existence
witness and the polynomial certificate for every compatible measure. -/
theorem isPadicPairLPolynomial_twist :
    IsPadicPairLPolynomial F ψ ν (twist (χ.comp determinant) π)
        (twist ((χ⁻¹).comp determinant) σ) P ↔
      IsPadicPairLPolynomial F ψ ν π σ P := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  exact imp_congr_right fun _ => isPairLPolynomial_twist χ

/-- The same full L-certificate transport for both rank orders, with the
original order retained in the equal-rank branch. -/
theorem isPadicSymmetricLPolynomial_twist :
    IsPadicSymmetricLPolynomial F ψ ν (twist (χ.comp determinant) π)
        (twist ((χ⁻¹).comp determinant) σ) P ↔
      IsPadicSymmetricLPolynomial F ψ ν π σ P := by
  unfold IsPadicSymmetricLPolynomial
  split_ifs
  · exact isPadicPairLPolynomial_twist ψ ν π σ χ P
  · have hinv : (χ⁻¹)⁻¹ = χ :=
      MonoidHom.ext fun x => by change (χ x)⁻¹⁻¹ = χ x; exact inv_inv _
    simpa only [hinv] using
      isPadicPairLPolynomial_twist ψ ν σ π χ⁻¹ P

end LTwist

section ScalarTest

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : letI := borel F
    AdditiveHaarMeasure F)
  (χ : Quasicharacter F)
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Move a scalar test character to a determinant twist of the other
representation, without changing the full symmetric L certificate. -/
theorem isPadicSymmetricLPolynomial_rankOne_test_twist (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν (rankOneCharacter 1)
        (twist ((χ : Fˣ →* ℂˣ).comp determinant) π) P ↔
      IsPadicSymmetricLPolynomial F ψ ν (rankOneCharacter (χ : Fˣ →* ℂˣ))
        π P := by
  have hchar :
      twist (((χ : Fˣ →* ℂˣ)⁻¹).comp determinant)
          (rankOneCharacter (χ : Fˣ →* ℂˣ)) =
        rankOneCharacter (1 : Fˣ →* ℂˣ) := by
    have hone : (1 : Fˣ →* ℂˣ) * (χ : Fˣ →* ℂˣ) = χ :=
      MonoidHom.ext fun _ => one_mul _
    simpa only [hone] using
      twist_rankOneCharacter (χ := (1 : Fˣ →* ℂˣ)) (χ : Fˣ →* ℂˣ)
  have hinv : ((χ : Fˣ →* ℂˣ)⁻¹)⁻¹ = χ :=
    MonoidHom.ext fun x => by change (χ x)⁻¹⁻¹ = χ x; exact inv_inv _
  simpa only [hchar, hinv] using
    isPadicSymmetricLPolynomial_twist ψ ν
      (rankOneCharacter (χ : Fˣ →* ℂˣ)) π (χ : Fˣ →* ℂˣ)⁻¹ P

/-- The analogous gamma transport with the scalar test first. Full type is
needed only for the equal-rank exchange; positive rank uses the larger-first
definition directly. -/
theorem isPadicSymmetricGammaFactor_rankOne_test_twist
    (hπ : n = 0 → IsOfWhittakerType n (standardCharacter ψ n) π)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ ν (rankOneCharacter 1)
        (twist ((χ : Fˣ →* ℂˣ).comp determinant) π) G ↔
      IsPadicSymmetricGammaFactor F ψ ν (rankOneCharacter (χ : Fˣ →* ℂˣ))
        π G := by
  by_cases hn : n = 0
  · subst n
    have hπ₀ := hπ rfl
    have hπχ := (isOfWhittakerType_quasicharacter_twist_iff
      (⟨⟩ : LocalFieldData F) ψ χ π).2 hπ₀
    have hχ := rankOneCharacter_isOfWhittakerType F ψ χ
    have h1 := rankOneCharacter_isOfWhittakerType F ψ 1
    have ht := rankOneGammaTwist F ψ ν 0 π (χ : Fˣ →* ℂˣ) G
    simp only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true] at ht ⊢
    exact (isPadicPairGammaFactor_swap_equalRank F ψ ν
      (rankOneCharacter 1) _ h1 hπχ G).trans
        (ht.trans (isPadicPairGammaFactor_swap_equalRank F ψ ν π
          (rankOneCharacter (χ : Fˣ →* ℂˣ)) hπ₀ hχ G))
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simpa only [IsPadicSymmetricGammaFactor, Nat.zero_le, Nat.not_le.mpr hnpos,
      ite_true, ite_false] using
      rankOneGammaTwist F ψ ν n π (χ : Fˣ →* ℂˣ) G

end ScalarTest

/-- A two-block gamma theorem for the trivial scalar test suffices for the
published arbitrary-carrier rank-one target. The analytic premise is explicit. -/
theorem twoBlockGammaRankOne_of_trivial_test
    (hbase : ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      (ψ : UnitaryAdditiveCharacter F)
      (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
      (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
      ∃ G : Fin 2 → RationalFunctions,
        (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val (rankOneCharacter 1) (σ i) (G i)) ∧
        IsPadicSymmetricGammaFactor F ψ ν.val (rankOneCharacter 1)
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)) :
    TwoBlockGammaRankOneStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r t m h V _ _ W _ _ π σ hr hπ hσ
  subst r
  obtain ⟨χ, ⟨eπ⟩⟩ := rankOneCharacterReduction F ψ V π hπ
  let σχ (i : Fin 2) := twist ((χ : Fˣ →* ℂˣ).comp determinant) (σ i)
  have hσχ (i : Fin 2) :
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σχ i) :=
    (isOfWhittakerType_quasicharacter_twist_iff
      (⟨⟩ : LocalFieldData F) ψ χ (σ i)).2 (hσ i)
  obtain ⟨G, hG, hI⟩ := hbase F ψ ν t m h σχ hσχ
  have ht : 0 < t := by
    rw [Fin.sum_univ_two] at h
    omega
  let eI := (⟨⟩ : LocalFieldData F).normalizedProductDeterminantTwistEquiv
    (succBlockShape m h) (quasicharacterSmoothCharacter (⟨⟩ : LocalFieldData F) χ) σ
  refine ⟨G, fun i => ?_, ?_⟩
  · apply (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv eπ
      (Representation.Equiv.refl (σ i))).2
    exact (isPadicSymmetricGammaFactor_rankOne_test_twist ψ ν.val χ (σ i)
      (fun _ => hσ i) (G i)).1 (hG i)
  · apply (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv eπ
      (Representation.Equiv.refl _)).2
    apply (isPadicSymmetricGammaFactor_rankOne_test_twist ψ ν.val χ
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
      (fun ht0 => (Nat.ne_of_gt ht ht0).elim) (∏ i, G i)).1
    exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv
      (Representation.Equiv.refl _) eI).2 hI

/-- A two-block L theorem for the trivial scalar test suffices for the
published arbitrary-carrier target, preserving the exact polynomial identity. -/
theorem twoBlockLRankOne_of_trivial_test
    (hbase : ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      (ψ : UnitaryAdditiveCharacter F)
      (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
      (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
      ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
        IsPadicSymmetricLPolynomial F ψ ν.val (rankOneCharacter 1)
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
        (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val
          (rankOneCharacter 1) (σ i) (Pi i)) ∧
        ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P) :
    TwoBlockLRankOneStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r t m h V _ _ W _ _ π σ hr hπ hσ
  subst r
  obtain ⟨χ, ⟨eπ⟩⟩ := rankOneCharacterReduction F ψ V π hπ
  let σχ (i : Fin 2) := twist ((χ : Fˣ →* ℂˣ).comp determinant) (σ i)
  have hσχ (i : Fin 2) :
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σχ i) :=
    (isOfWhittakerType_quasicharacter_twist_iff
      (⟨⟩ : LocalFieldData F) ψ χ (σ i)).2 (hσ i)
  obtain ⟨P, Pi, hP, hPi, hdiv⟩ := hbase F ψ ν t m h σχ hσχ
  let eI := (⟨⟩ : LocalFieldData F).normalizedProductDeterminantTwistEquiv
    (succBlockShape m h) (quasicharacterSmoothCharacter (⟨⟩ : LocalFieldData F) χ) σ
  refine ⟨P, Pi, ?_, fun i => ?_, hdiv⟩
  · apply (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv eπ
      (Representation.Equiv.refl _)).2
    apply (isPadicSymmetricLPolynomial_rankOne_test_twist ψ ν.val χ
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P).1
    exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv
      (Representation.Equiv.refl _) eI).2 hP
  · apply (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv eπ
      (Representation.Equiv.refl (σ i))).2
    exact (isPadicSymmetricLPolynomial_rankOne_test_twist ψ ν.val χ (σ i)
      (Pi i)).1 (hPi i)

end Langlands.AllField.RankinSelberg
