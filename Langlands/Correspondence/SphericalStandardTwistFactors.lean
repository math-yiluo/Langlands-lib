import Langlands.Automorphic.AssociatedGammaPrincipalSeries
import Langlands.Correspondence.UnramifiedPairFactors
import Langlands.Group.GL.RankReindex
import Langlands.Representation.Induction.SingleBlock

/-! # Standard factors of determinant twists of spherical representations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Correspondence

open GeneralLinear Unramified RankinSelberg
open LocalFactor.PadicAbelian (lPolynomial epsilonExponent)

universe uF uA uB

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance sphericalStandardTwistFactorsIsTopologicalGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

local notation "T" => F.canonicalTopologicalData

private abbrev characterBlock (χ : QuasiCharacter F) :
    SmoothRep.{0, uF, uA} ℂ (GeneralLinear 1 F.Carrier) :=
  (rankOneSupercuspidalObject.{uF, uA} F χ).obj

private theorem characterBlock_squareIntegrable (χ : QuasiCharacter F) :
    (T).IsEssentiallySquareIntegrable (characterBlock.{uF, uA} F χ).representation :=
  supercuspidal_isEssentiallySquareIntegrable F 0 _
    (rankOneSupercuspidalObject.{uF, uA} F χ).property.1
    (rankOneSupercuspidalObject.{uF, uA} F χ).property.2

private def characterBlockExponent (χ : QuasiCharacter F) :
    UnitaryExponentData ((T).determinantNorm 1) (characterBlock.{uF, uA} F χ).representation :=
  ((T).nonempty_unitaryExponentData Nat.one_pos
    (rankOneSupercuspidalObject.{uF, uA} F χ).property.1
    (characterBlock_squareIntegrable F χ)).some

private theorem characterBlock_norm_eq_rpow (χ : QuasiCharacter F)
    (a : UnitaryExponentData ((T).determinantNorm 1) (characterBlock.{uF, uA} F χ).representation) :
    ‖(χ (T).uniformizerUnit : ℂ)‖ = (T).normalizedAbs (T).uniformizer ^ a.exponent := by
  have : Nontrivial (characterBlock.{uF, uA} F χ) := by
    change Nontrivial (ULift.{uA} ℂ)
    infer_instance
  have h := unitaryExponentScalarNorm.{uF, uA} (GeneralLinear 1 F.Carrier)
    (characterBlock.{uF, uA} F χ) ((T).determinantNorm 1)
    (characterBlock.{uF, uA} F χ).representation a (uniformizerElement F)
    (χ (T).uniformizerUnit : ℂ) (fun v => by
      change (χ (determinant (uniformizerElement F)) : ℂ) • v = _
      rw [determinant_uniformizerElement])
  rw [h, PadicField.TopologicalData.determinantNorm_coe, determinant_uniformizerElement]
  rfl

/-- Ordered Langlands data on the Borel with continuous rank-one characters
as blocks. The order is determined by the norms of their uniformizer values. -/
def characterDatum {r : ℕ} (χ : Fin (r + 1) → QuasiCharacter F)
    (hχ : Monotone fun i => ‖(χ i (T).uniformizerUnit : ℂ)‖) :
    PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{uA, uF} T (r + 1) where
  shape := borelShape r
  blocks i := characterBlock.{uF, uA} F (χ i)
  irreducible i := (rankOneSupercuspidalObject.{uF, uA} F (χ i)).property.1
  essentiallySquareIntegrable i := characterBlock_squareIntegrable F (χ i)
  unitaryExponent i := characterBlockExponent F (χ i)
  antitone i j hij := by
    obtain ⟨hb0, hb1⟩ := uniformizer_norm_bounds F
    have h : ‖(χ i (T).uniformizerUnit : ℂ)‖ ≤ ‖(χ j (T).uniformizerUnit : ℂ)‖ := hχ hij
    rw [characterBlock_norm_eq_rpow F (χ i) (characterBlockExponent F (χ i)),
      characterBlock_norm_eq_rpow F (χ j) (characterBlockExponent F (χ j))] at h
    exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hb1).mp h

private def characterDatumInducedEquiv {r : ℕ} (χ : Fin (r + 1) → QuasiCharacter F)
    (hχ : Monotone fun i => ‖(χ i (T).uniformizerUnit : ℂ)‖) :
    (characterDatum.{uF, uA} F χ hχ).induced.representation.Equiv (principalSeries F r χ) := by
  unfold principalSeries
  refine (T).normalizedProductInducedEquiv (borelShape r) (fun i => ?_)
  exact Representation.Equiv.mk ULift.moduleEquiv (fun g => by ext v; rfl)

/-- A common character multiplies all uniformizer norms by the same positive number. -/
theorem monotone_unramifiedCharacter_mul {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone fun i => ‖(z i : ℂ)‖) (ω : QuasiCharacter F) :
    Monotone fun i => ‖((character F (z i) * ω) (T).uniformizerUnit : ℂ)‖ := by
  intro i j hij
  change ‖((character F (z i) (T).uniformizerUnit * ω (T).uniformizerUnit : ℂˣ) : ℂ)‖ ≤
    ‖((character F (z j) (T).uniformizerUnit * ω (T).uniformizerUnit : ℂˣ) : ℂ)‖
  simp only [Units.val_mul, norm_mul, character_uniformizer]
  exact mul_le_mul_of_nonneg_right (hz hij) (norm_nonneg _)

set_option maxHeartbeats 1000000 in
/-- Twisting a quotient of an ordered unramified principal series gives a
quotient of the inducing characters twisted by the common determinant character. -/
theorem unramifiedDatum_twist_isLanglandsQuotient {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone fun i => ‖(z i : ℂ)‖) (ω : QuasiCharacter F)
    (J Jω : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (hJ : (unramifiedDatum.{uF, uA} F z hz).IsLanglandsQuotient J)
    (e : (Langlands.twist (determinantQuasiCharacter F r.succPNat ω)
        J.representation).Equiv Jω.representation) :
    (characterDatum.{uF, uA} F (fun i => character F (z i) * ω)
      (monotone_unramifiedCharacter_mul F z hz ω)).IsLanglandsQuotient Jω := by
  let a := Langlands.twistEquiv (determinantQuasiCharacter F r.succPNat ω)
    (unramifiedDatumInducedEquiv.{uF, uA} F z hz)
  let b := principalSeriesTwistEquiv F (fun i => character F (z i)) ω
  let c := characterDatumInducedEquiv.{uF, uA} F (fun i => character F (z i) * ω)
    (monotone_unramifiedCharacter_mul F z hz ω)
  let d := (a.trans b).trans c.symm
  obtain ⟨hJirr, q, hq⟩ := hJ
  have hJωirr := (Langlands.isIrreducible_iff_of_equiv e).mp
    ((Langlands.isIrreducible_twist_iff _ _).mpr hJirr)
  let qω := Langlands.twistIntertwining (determinantQuasiCharacter F r.succPNat ω) q
  let q' := e.toIntertwiningMap.comp (qω.comp d.symm.toIntertwiningMap)
  have hqω : Function.Surjective qω := hq
  exact ⟨hJωirr, q', e.surjective.comp (hqω.comp d.symm.surjective)⟩

private def trivialRankOneDatum : PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{uB, uF}
    T 1 := characterDatum F (fun _ : Fin 1 => 1) monotone_const

private theorem trivialRankOneDatum_isLanglandsQuotient
    (J : SmoothRep.{0, uF, max uF uB} ℂ (GeneralLinear 1 F.Carrier))
    (e : (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J.representation) :
    (trivialRankOneDatum.{uF, uB} F).IsLanglandsQuotient J := by
  let d := trivialRankOneDatum.{uF, uB} F
  let i₀ : Fin d.shape.length := ⟨0, Nat.one_pos⟩
  let a : d.induced.representation.Equiv (d.blocks i₀).representation := by
    let a₀ := (T).singleBlockNormalizedProductEquiv d.shape (show d.shape.length = 1 from rfl)
      (fun j => (d.blocks j).representation) (fun j => (d.blocks j).isSmooth) i₀
    refine Representation.Equiv.mk a₀.toLinearEquiv fun g => LinearMap.ext fun x => ?_
    have hg := a₀.isIntertwining' g
    change a₀.toLinearEquiv.toLinearMap ∘ₗ d.induced.representation g =
      (d.blocks i₀).representation
        ((reindex (R := F.Carrier) (finCongr (rfl : 1 = 1))).symm g) ∘ₗ
        a₀.toLinearEquiv.toLinearMap at hg
    rw [reindex_finCongr_rfl] at hg
    change a₀.toLinearEquiv (d.induced.representation g x) =
      (d.blocks i₀).representation g (a₀.toLinearEquiv x)
    exact LinearMap.congr_fun hg x
  let b : (d.blocks i₀).representation.Equiv (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) :=
    FiniteRepresentation.characterLineEquiv (determinantQuasiCharacter F 1 1)
  let c : d.induced.representation.Equiv J.representation := a.trans (b.trans e)
  refine ⟨?_, c.toIntertwiningMap, c.surjective⟩
  exact (Langlands.isIrreducible_iff_of_equiv (b.trans e)).mp (d.irreducible i₀)

/-- The standard L-polynomial and epsilon exponent for an ordered quotient of
continuous rank-one inducing characters are their Tate product and sum. -/
theorem standardFactors_of_characterDatum {r : ℕ}
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν)
    (χ : Fin (r + 1) → QuasiCharacter F) (hχ : Monotone fun i => ‖(χ i (T).uniformizerUnit : ℂ)‖)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J₁ : SmoothRep.{0, uF, max uF uB} ℂ (GeneralLinear 1 F.Carrier))
    (hJ : (characterDatum.{uF, uA} F χ hχ).IsLanglandsQuotient J)
    (e₁ : (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁.representation)
    {P : Polynomial ℂ} {b : ℂˣ × ℤ}
    (hP : IsLanglandsPairLPolynomial.{uF, uA, uB} F ψ ν J J₁ P)
    (hb : IsLanglandsPairEpsilonFactor.{uF, uA, uB} F ψ ν J J₁ b) :
    P = (∏ i, lPolynomial T (χ i)) ∧ b.2 = ∑ i, epsilonExponent T (χ i) ψ := by
  let d := characterDatum.{uF, uA} F χ hχ
  let d₁ := trivialRankOneDatum.{uF, uB} F
  have hJ₁ := trivialRankOneDatum_isLanglandsQuotient F J₁ e₁
  let a (i : Fin d.shape.length) :
      (rankOneCharacter (χ i).toMonoidHom).Equiv (d.blocks i).representation :=
    (FiniteRepresentation.characterLineEquiv (determinantQuasiCharacter F 1 (χ i))).symm
  let a₁ (j : Fin d₁.shape.length) :
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv (d₁.blocks j).representation :=
    (FiniteRepresentation.characterLineEquiv (determinantQuasiCharacter F 1 1)).symm
  have hmul (i : Fin (r + 1)) : χ i * (1 : QuasiCharacter F) = χ i := by
    apply ContinuousMonoidHom.ext
    intro x
    change χ i x * 1 = _
    exact mul_one _
  obtain ⟨P₀, Q, hP₀, hQ, hPQ⟩ := squareIntegrableDataLFactor.{uF, uA, uB}
    p F ψ ⟨ν, hν⟩ r 0 d d₁ J J₁ hJ hJ₁
  obtain ⟨b₀, hb₀, rfl⟩ := hb.2.2 d d₁ hJ hJ₁
  constructor
  · have hpoly (i : Fin d.shape.length) (j : Fin d₁.shape.length) :
        Q i j = lPolynomial T (χ i) := by
      have h := isPadicPairLPolynomial_of_rankOneCharacterEquiv F ψ ν (a i) (a₁ j)
        (η := (1 : QuasiCharacter F))
      have h' := (isPadicSymmetricLPolynomial_of_le (Nat.le_refl 0)).mpr h
      simpa only [hmul] using ((isPadicRankLPolynomial_succ.mp (hQ i j)).unique h')
    rw [hP.unique hP₀, hPQ]
    simp_rw [hpoly]
    change (∏ i : Fin (r + 1), ∏ _ : Fin 1, lPolynomial T (χ i)) = _
    simp
  · have hexp (i : Fin d.shape.length) (j : Fin d₁.shape.length) :
        (b₀ i j).2 = epsilonExponent T (χ i) ψ := by
      have h := isPadicPairEpsilonFactor_rankOneCharacterEquiv_gauss F ψ ν hν (a i) (a₁ j)
        (η := (1 : QuasiCharacter F))
      have h' := (isPadicSymmetricEpsilonFactor_of_le (Nat.le_refl 0)).mpr h
      simpa only [hmul] using congrArg Prod.snd ((hb₀ i j).unique h')
    simp only [epsilonFactorProduct, hexp]
    change (∑ i : Fin (r + 1), ∑ _ : Fin 1, epsilonExponent T (χ i) ψ) = _
    simp

/-- The standard factors for a determinant twist use the pointwise twisted
unramified inducing characters, including when the common character is ramified. -/
def SphericalStandardTwistFactorsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F),
    IsSelfDualMeasure F ψ ν →
    ∀ (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖)
      (ω : QuasiCharacter F)
      (J Jω : letI := F.canonicalTopologicalData.topology
        SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
      (J₁ : letI := F.canonicalTopologicalData.topology
        SmoothRep.{0, uF, max uF uB} ℂ (GeneralLinear 1 F.Carrier)),
      (unramifiedDatum.{uF, uA} F z hz).IsLanglandsQuotient J →
      Nonempty ((Langlands.twist (determinantQuasiCharacter F r.succPNat ω)
        J.representation).Equiv Jω.representation) →
      Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁.representation) →
      ∀ (P : Polynomial ℂ) (b : ℂˣ × ℤ),
        IsLanglandsPairLPolynomial.{uF, uA, uB} F ψ ν Jω J₁ P →
        IsLanglandsPairEpsilonFactor.{uF, uA, uB} F ψ ν Jω J₁ b →
        P = (∏ i, lPolynomial F.canonicalTopologicalData (character F (z i) * ω)) ∧
        b.2 = ∑ i, epsilonExponent F.canonicalTopologicalData (character F (z i) * ω) ψ

theorem sphericalStandardTwistFactors : SphericalStandardTwistFactorsStatement.{uF, uA, uB} := by
  intro p _ F r ψ ν hν z hz ω J Jω J₁ hJ ⟨e⟩ ⟨e₁⟩ P b hP hb
  exact standardFactors_of_characterDatum F ψ ν hν _ _ Jω J₁
    (unramifiedDatum_twist_isLanglandsQuotient F z hz ω J Jω hJ e) e₁ hP hb

end Langlands.Correspondence
