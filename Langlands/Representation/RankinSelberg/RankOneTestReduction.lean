import Langlands.Representation.RankinSelberg.TwoBlockBaseCasesStatement
import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.RankOneGammaTwistProof
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.Induction.NormalizedProductCharacterTwist

/-! # Reduction of rank-one tests to the trivial scalar test -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- A continuous complex character of the scalar group of a supplied p-adic
realization has open kernel. -/
theorem quasicharacter_isOpen_ker {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (χ : letI := T.topology; Quasicharacter F.Carrier) :
    letI := T.topology
    IsOpen ((χ : F.Carrierˣ →* ℂˣ).ker : Set F.Carrierˣ) := by
  let := T.topology
  let := T.generalLinearNonarchimedean 1
  let χdet : Langlands.GeneralLinear 1 F.Carrier →* ℂˣ :=
    (χ : F.Carrierˣ →* ℂˣ).comp determinant
  have hopen : IsOpen (χdet.ker : Set (Langlands.GeneralLinear 1 F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character χdet
      (χ.continuous.comp (T.generalLinearDeterminant 1).continuous)
  convert hopen.preimage (scalarContinuous (R := F.Carrier) (n := 1)).continuous using 1
  ext x
  change χ x = 1 ↔ χ (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (R := F.Carrier) (Fin 1) x)) = 1
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]

/-- The same scalar character, packaged with the open kernel needed for actual
smooth normalized induction. -/
def quasicharacterSmoothCharacter {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (χ : letI := T.topology; Quasicharacter F.Carrier) :
    letI := T.topology
    Induction.SmoothCharacter ℂ F.Carrierˣ := by
  let := T.topology
  exact ⟨(χ : F.Carrierˣ →* ℂˣ), quasicharacter_isOpen_ker T χ⟩

/-- Continuous determinant twists retain all three parts of full Whittaker
type, on an arbitrary carrier. -/
theorem isOfWhittakerType_quasicharacter_twist_iff {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := T.topology; Quasicharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    IsOfWhittakerType n (standardCharacter ψ n)
        (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ↔
      IsOfWhittakerType n (standardCharacter ψ n) π := by
  let := T.topology
  apply isOfWhittakerType_twist_iff
  · exact (quasicharacter_isOpen_ker T χ).preimage
      (T.generalLinearDeterminant (n + 1)).continuous
  · exact determinantCharacter_unipotent _

section LTwist

variable {F : PadicField.{uF} p}
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (χ : F.Carrierˣ →* ℂˣ) (P : ℂ[X])

/-- Opposite determinant twists preserve the quotient-measure existence
witness and the polynomial certificate for every compatible measure. -/
theorem isPadicPairLPolynomial_twist :
    IsPadicPairLPolynomial F ψ ν (twist (χ.comp determinant) π)
        (twist ((χ⁻¹).comp determinant) σ) P ↔
      IsPadicPairLPolynomial F ψ ν π σ P := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
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

variable {F : PadicField.{uF} p}
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)

/-- Move a scalar test character to a determinant twist of the other
representation, without changing the full symmetric L certificate. -/
theorem isPadicSymmetricLPolynomial_rankOne_test_twist (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν (rankOneCharacter 1)
        (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) P ↔
      IsPadicSymmetricLPolynomial F ψ ν (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
        π P := by
  have hchar :
      twist (((χ : F.Carrierˣ →* ℂˣ)⁻¹).comp determinant)
          (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) =
        rankOneCharacter (1 : F.Carrierˣ →* ℂˣ) := by
    have hone : (1 : F.Carrierˣ →* ℂˣ) * (χ : F.Carrierˣ →* ℂˣ) = χ :=
      MonoidHom.ext fun _ => one_mul _
    simpa only [hone] using
      twist_rankOneCharacter (χ := (1 : F.Carrierˣ →* ℂˣ)) (χ : F.Carrierˣ →* ℂˣ)
  have hinv : ((χ : F.Carrierˣ →* ℂˣ)⁻¹)⁻¹ = χ :=
    MonoidHom.ext fun x => by change (χ x)⁻¹⁻¹ = χ x; exact inv_inv _
  simpa only [hchar, hinv] using
    isPadicSymmetricLPolynomial_twist ψ ν
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) π (χ : F.Carrierˣ →* ℂˣ)⁻¹ P

/-- The analogous gamma transport with the scalar test first. Full type is
needed only for the equal-rank exchange; positive rank uses the larger-first
definition directly. -/
theorem isPadicSymmetricGammaFactor_rankOne_test_twist
    (hπ : n = 0 → letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) π)
    (G : RationalFunctions) :
    IsPadicSymmetricGammaFactor F ψ ν (rankOneCharacter 1)
        (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) G ↔
      IsPadicSymmetricGammaFactor F ψ ν (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
        π G := by
  let := F.canonicalTopologicalData.topology
  by_cases hn : n = 0
  · subst n
    have hπ₀ := hπ rfl
    have hπχ := (isOfWhittakerType_quasicharacter_twist_iff
      F.canonicalTopologicalData ψ χ π).2 hπ₀
    have hχ := rankOneCharacter_isOfWhittakerType p F ψ χ
    have h1 := rankOneCharacter_isOfWhittakerType p F ψ 1
    have ht := rankOneGammaTwist p F ψ ν 0 π (χ : F.Carrierˣ →* ℂˣ) G
    simp only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true] at ht ⊢
    exact (isPadicPairGammaFactor_swap_equalRank F ψ ν
      (rankOneCharacter 1) _ h1 hπχ G).trans
        (ht.trans (isPadicPairGammaFactor_swap_equalRank F ψ ν π
          (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) hπ₀ hχ G))
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simpa only [IsPadicSymmetricGammaFactor, Nat.zero_le, Nat.not_le.mpr hnpos,
      ite_true, ite_false] using
      rankOneGammaTwist p F ψ ν n π (χ : F.Carrierˣ →* ℂˣ) G

end ScalarTest

/-- A two-block gamma theorem for the trivial scalar test suffices for the
published arbitrary-carrier rank-one target. The analytic premise is explicit. -/
theorem twoBlockGammaRankOne_of_trivial_test
    (hbase : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
      (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
      (∀ i, letI := F.canonicalTopologicalData.topology
        IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
      ∃ G : Fin 2 → RationalFunctions,
        (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val (rankOneCharacter 1) (σ i) (G i)) ∧
        IsPadicSymmetricGammaFactor F ψ ν.val (rankOneCharacter 1)
          (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)) :
    TwoBlockGammaRankOneStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t m h V _ _ W _ _ π σ hr hπ hσ
  subst r
  let := F.canonicalTopologicalData.topology
  obtain ⟨χ, ⟨eπ⟩⟩ := rankOneCharacterReduction p F ψ V π hπ
  let σχ (i : Fin 2) := twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) (σ i)
  have hσχ (i : Fin 2) :
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σχ i) :=
    (isOfWhittakerType_quasicharacter_twist_iff
      F.canonicalTopologicalData ψ χ (σ i)).2 (hσ i)
  obtain ⟨G, hG, hI⟩ := hbase p F ψ ν t m h σχ hσχ
  have ht : 0 < t := by
    rw [Fin.sum_univ_two] at h
    omega
  let eI := F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv
    (succBlockShape m h) (quasicharacterSmoothCharacter F.canonicalTopologicalData χ) σ
  refine ⟨G, fun i => ?_, ?_⟩
  · apply (IsPadicSymmetricGammaFactor.congr_equiv eπ
      (Representation.Equiv.refl (σ i))).2
    exact (isPadicSymmetricGammaFactor_rankOne_test_twist ψ ν.val χ (σ i)
      (fun _ => hσ i) (G i)).1 (hG i)
  · apply (IsPadicSymmetricGammaFactor.congr_equiv eπ
      (Representation.Equiv.refl _)).2
    apply (isPadicSymmetricGammaFactor_rankOne_test_twist ψ ν.val χ
      (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)
      (fun ht0 => (Nat.ne_of_gt ht ht0).elim) (∏ i, G i)).1
    exact (IsPadicSymmetricGammaFactor.congr_equiv
      (Representation.Equiv.refl _) eI).2 hI

/-- A two-block L theorem for the trivial scalar test suffices for the
published arbitrary-carrier target, preserving the exact polynomial identity. -/
theorem twoBlockLRankOne_of_trivial_test
    (hbase : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
      (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
      (∀ i, letI := F.canonicalTopologicalData.topology
        IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
      ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
        IsPadicSymmetricLPolynomial F ψ ν.val (rankOneCharacter 1)
          (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P ∧
        (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val
          (rankOneCharacter 1) (σ i) (Pi i)) ∧
        ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P) :
    TwoBlockLRankOneStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t m h V _ _ W _ _ π σ hr hπ hσ
  subst r
  let := F.canonicalTopologicalData.topology
  obtain ⟨χ, ⟨eπ⟩⟩ := rankOneCharacterReduction p F ψ V π hπ
  let σχ (i : Fin 2) := twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) (σ i)
  have hσχ (i : Fin 2) :
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σχ i) :=
    (isOfWhittakerType_quasicharacter_twist_iff
      F.canonicalTopologicalData ψ χ (σ i)).2 (hσ i)
  obtain ⟨P, Pi, hP, hPi, hdiv⟩ := hbase p F ψ ν t m h σχ hσχ
  let eI := F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv
    (succBlockShape m h) (quasicharacterSmoothCharacter F.canonicalTopologicalData χ) σ
  refine ⟨P, Pi, ?_, fun i => ?_, hdiv⟩
  · apply (IsPadicSymmetricLPolynomial.congr_equiv eπ
      (Representation.Equiv.refl _)).2
    apply (isPadicSymmetricLPolynomial_rankOne_test_twist ψ ν.val χ
      (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P).1
    exact (IsPadicSymmetricLPolynomial.congr_equiv
      (Representation.Equiv.refl _) eI).2 hP
  · apply (IsPadicSymmetricLPolynomial.congr_equiv eπ
      (Representation.Equiv.refl (σ i))).2
    exact (isPadicSymmetricLPolynomial_rankOne_test_twist ψ ν.val χ (σ i)
      (Pi i)).1 (hPi i)

end Langlands.RankinSelberg
