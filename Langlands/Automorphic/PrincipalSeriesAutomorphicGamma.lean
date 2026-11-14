import Langlands.Automorphic.PrincipalSeriesRankOneGamma
import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.RankinSelberg.ComponentFactorComparisonProof
import Langlands.Representation.RankinSelberg.GammaMultiplicativityProof
import Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonProof
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.Whittaker.GelfandGraevJacquetOpen
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # Gamma factors of generic principal-series constituents -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Correspondence

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
private local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Simultaneous reindexing preserves the determinant. -/
theorem determinant_reindex_symm {a b : ℕ} (e : Fin a ≃ Fin b)
    (g : GeneralLinear b F.Carrier) :
    GeneralLinear.determinant ((GeneralLinear.reindex (R := F.Carrier) e).symm g) =
      GeneralLinear.determinant g := by
  have h : GeneralLinear.determinant (GeneralLinear.reindex (R := F.Carrier) e
      ((GeneralLinear.reindex (R := F.Carrier) e).symm g)) =
      GeneralLinear.determinant ((GeneralLinear.reindex (R := F.Carrier) e).symm g) := by
    apply Units.ext
    change Matrix.det (Matrix.reindex e e _) = Matrix.det _
    rw [Matrix.det_reindex_self]
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- The character representation `χ ∘ det` of `GL_1` is smooth. -/
theorem isSmooth_rankOneCharacter (χ : QuasiCharacter F) :
    IsSmooth (rankOneCharacter χ.toMonoidHom) := by
  let := F.canonicalGeneralLinearNonarchimedean 1
  let χdet : GeneralLinear 1 F.Carrier →* ℂˣ := χ.toMonoidHom.comp GeneralLinear.determinant
  have hopen : IsOpen (χdet.ker : Set (GeneralLinear 1 F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character χdet
      (χ.continuous.comp (F.canonicalTopologicalData.generalLinearDeterminant 1).continuous)
  apply (isSmooth_twist_iff χdet (Representation.trivial ℂ _ ℂ) hopen).mpr
  intro v
  exact ⟨⊤, fun _ => rfl⟩

/-- The one-block principal series `i(χ)` of `GL_1` is the character representation
`χ ∘ det`. -/
def principalSeriesZeroEquiv (μ : Fin 1 → QuasiCharacter F) :
    (rankOneCharacter (μ 0).toMonoidHom).Equiv (principalSeries F 0 μ) := by
  let τ : ∀ i : Fin (borelShape 0).length,
      Representation ℂ (GeneralLinear ((borelShape 0).size i) F.Carrier) ℂ :=
    fun i => characterRepresentation (determinantQuasiCharacter F 1 (μ i))
  have hτ : ∀ i, IsSmooth (τ i) := fun i =>
    isSmooth_rankOneCharacter F (μ i)
  let E := F.canonicalTopologicalData.singleBlockNormalizedProductEquiv (borelShape 0) rfl τ hτ
    ⟨0, Nat.one_pos⟩
  refine Representation.Equiv.trans ?_ E.symm
  refine (characterRepresentationEquiv _ (LinearEquiv.refl ℂ ℂ)
    ((μ 0).toMonoidHom.comp GeneralLinear.determinant) ?_).symm
  intro k v
  change ((μ 0).toMonoidHom (GeneralLinear.determinant
      ((GeneralLinear.reindex (R := F.Carrier) _).symm k)) : ℂ) • v = _
  rw [determinant_reindex_symm]
  rfl

private theorem sum_borelBlocks (t : ℕ) : ∑ _j : Fin (t + 1), (0 + 1) = t + 1 := by
  simp

/-- The normalized principal series is of Whittaker type. -/
theorem principalSeries_isOfWhittakerType (ψ : NontrivialAdditiveCharacter F) {t : ℕ}
    (μ : Fin (t + 1) → QuasiCharacter F) :
    IsOfWhittakerType t (standardCharacter ψ t) (principalSeries F t μ) :=
  normalizedProductWhittakerType p F ψ t (t + 1) (fun _ => 0) (sum_borelBlocks t)
    (fun j => characterRepresentation (determinantQuasiCharacter F 1 (μ j)))
    (fun j => rankOneCharacter_isOfWhittakerType p F ψ (μ j))

/-- `γ(χ × i(μ'))` is the product of Tate gamma factors `∏_j γ(χ μ'_j)`. -/
theorem isPadicSymmetricGammaFactor_rankOne_principalSeries
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν) (χ : QuasiCharacter F) {t : ℕ}
    (μ' : Fin (t + 1) → QuasiCharacter F) :
    IsPadicSymmetricGammaFactor F ψ ν (rankOneCharacter χ.toMonoidHom)
      (principalSeries F t μ') (∏ j, tateRationalGamma F ψ ν (χ * μ' j)) := by
  obtain ⟨G, hG, hprod⟩ := gammaMultiplicativity p F ψ ⟨ν, hν⟩ 0 t (t + 1) (fun _ => 0)
    (sum_borelBlocks t) (rankOneCharacter χ.toMonoidHom)
    (fun j => characterRepresentation (determinantQuasiCharacter F 1 (μ' j)))
    (rankOneCharacter_isOfWhittakerType p F ψ χ)
    (fun j => rankOneCharacter_isOfWhittakerType p F ψ (μ' j))
  have hGj : ∀ j, G j = tateRationalGamma F ψ ν (χ * μ' j) := fun j =>
    (hG j).unique ((isPadicSymmetricGammaFactor_of_le le_rfl).mpr
      (isPadicPairGammaFactor_rankOneCharacters F ψ ν hν χ (μ' j)))
  rw [Finset.prod_congr rfl (fun j _ => hGj j)] at hprod
  exact hprod

/-- `γ(i(μ) × χ)` is the product of Tate gamma factors `∏_i γ(μ_i χ)`. -/
theorem isPadicSymmetricGammaFactor_principalSeries_rankOne
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν) {r : ℕ} (μ : Fin (r + 1) → QuasiCharacter F)
    (χ : QuasiCharacter F) :
    IsPadicSymmetricGammaFactor F ψ ν (principalSeries F r μ)
      (rankOneCharacter χ.toMonoidHom) (∏ i, tateRationalGamma F ψ ν (μ i * χ)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h := (isPadicSymmetricGammaFactor_of_le le_rfl).mpr
      (isPadicPairGammaFactor_rankOneCharacters F ψ ν hν (μ 0) χ)
    rw [Fin.prod_univ_one]
    exact (IsPadicSymmetricGammaFactor.congr_equiv (principalSeriesZeroEquiv F μ)
      (Representation.Equiv.refl _)).mp h
  · have h := isPadicSymmetricGammaFactor_rankOne_principalSeries F ψ ν hν χ μ
    simp_rw [mul_comm χ] at h
    exact (isPadicSymmetricGammaFactor_of_le (Nat.zero_le r)).mpr
      ((isPadicSymmetricGammaFactor_of_lt hr).mp h)

/-- `γ(i(μ) × i(μ'))` is the double product `∏_j ∏_i γ(μ_i μ'_j)`. -/
theorem isPadicSymmetricGammaFactor_principalSeries
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν) {r t : ℕ} (μ : Fin (r + 1) → QuasiCharacter F)
    (μ' : Fin (t + 1) → QuasiCharacter F) :
    IsPadicSymmetricGammaFactor F ψ ν (principalSeries F r μ) (principalSeries F t μ')
      (∏ j, ∏ i, tateRationalGamma F ψ ν (μ i * μ' j)) := by
  obtain ⟨G, hG, hprod⟩ := gammaMultiplicativity p F ψ ⟨ν, hν⟩ r t (t + 1) (fun _ => 0)
    (sum_borelBlocks t) (principalSeries F r μ)
    (fun j => characterRepresentation (determinantQuasiCharacter F 1 (μ' j)))
    (principalSeries_isOfWhittakerType F ψ μ)
    (fun j => rankOneCharacter_isOfWhittakerType p F ψ (μ' j))
  have hGj : ∀ j, G j = ∏ i, tateRationalGamma F ψ ν (μ i * μ' j) := fun j =>
    (hG j).unique (isPadicSymmetricGammaFactor_principalSeries_rankOne F ψ ν hν μ (μ' j))
  rw [Finset.prod_congr rfl (fun j _ => hGj j)] at hprod
  exact hprod

/-- The certified class gamma factor of generic irreducible subquotients of two
normalized principal series `i(μ)`, `i(μ')` is `∏_j ∏_i γ(μ_i μ'_j)`. -/
theorem isAutomorphicPairGammaFactor_principalSeries
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν) {r t : ℕ} (μ : Fin (r + 1) → QuasiCharacter F)
    (μ' : Fin (t + 1) → QuasiCharacter F)
    (A : AutomorphicObject.{uF, uF} F r.succPNat)
    (A' : AutomorphicObject.{uF, uF} F t.succPNat)
    (hA : Whittaker.IsGeneric ψ r A.obj.representation)
    (hsA : IsSubquotientOf (principalSeries F r μ) A.obj.representation)
    (hA' : Whittaker.IsGeneric ψ t A'.obj.representation)
    (hsA' : IsSubquotientOf (principalSeries F t μ') A'.obj.representation) :
    IsAutomorphicPairGammaFactor F ψ ν (automorphicClassOf F A) (automorphicClassOf F A')
      (∏ j, ∏ i, tateRationalGamma F ψ ν (μ i * μ' j)) := by
  obtain ⟨P, hP⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial
    F ψ hν (automorphicClassOf F A) (automorphicClassOf F A')
  obtain ⟨Pd, hPd⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial
    F ψ hν (SmoothDualClass.contragredient
      (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData r.succPNat)
      (automorphicClassOf F A))
    (SmoothDualClass.contragredient
      (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData t.succPNat)
      (automorphicClassOf F A'))
  obtain ⟨e, he⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairEpsilonFactor
    F ψ hν (automorphicClassOf F A) (automorphicClassOf F A')
  let G0 := automorphicPairGammaFactor
    ((isSmoothDual_iff_eq_contragredient F _ _).mpr rfl)
    ((isSmoothDual_iff_eq_contragredient F _ _).mpr rfl) hP hPd he
  have hsym := G0.2.isPadicSymmetricGammaFactor_of_generic (ν := ⟨ν, hν⟩)
    genericLanglandsPairEpsilonFactorComparison A A' hA hA'
  have heq := (componentFactorComparison p F ψ ν r t A.obj.representation
    A'.obj.representation (principalSeries F r μ) (principalSeries F t μ')
    (F.canonicalTopologicalData.isSmooth_normalizedProductInduced _ _)
    (F.canonicalTopologicalData.isSmooth_normalizedProductInduced _ _)
    ⟨hA.1, hsA⟩ ⟨hA'.1, hsA'⟩).1 _ _ hsym
    (isPadicSymmetricGammaFactor_principalSeries F ψ ν hν μ μ')
  rw [← heq]
  exact G0.2

end Langlands.Correspondence
