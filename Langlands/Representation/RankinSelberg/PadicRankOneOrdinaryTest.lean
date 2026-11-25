import Langlands.Representation.GodementJacquet.TateCharacterLFactor
import Langlands.Representation.GodementJacquet.TateCharacterReduction
import Langlands.Representation.RankinSelberg.PadicOrdinaryNormalizedTests

/-! An ordinary p-adic GL₁ pair test whose normalized integral is identically one. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GodementJacquet GeneralLinear
open scoped Polynomial

universe u uV uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

private local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
private local instance : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance : MeasurableSpace K.Carrier := borel _
local instance : BorelSpace K.Carrier := ⟨rfl⟩
local instance : MeasurableSpace K.Carrierˣ := borel _
local instance : BorelSpace K.Carrierˣ := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) K.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LeftUnipotentQuotient 0 K.Carrier) := borel _
local instance : BorelSpace (LeftUnipotentQuotient 0 K.Carrier) := ⟨rfl⟩

local notation "qK" => K.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue K.canonicalTopologicalData
local notation "μ" => unipotentQuotientHaar K.Carrier 0

/-- For an actual admissible irreducible rank-one pair, a single test with the
canonical quotient measure realizes the right-half-plane L-factor. -/
def PadicRankOneOrdinaryTestStatement : Prop :=
  ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear 1 K.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear 1 K.Carrier) W) (P : ℂ[X]),
    IsAdmissible π → π.IsIrreducible → IsAdmissible σ → σ.IsIrreducible →
    IsPadicPairLPolynomial K ψ ν π σ P →
    ∃ W₁ ∈ whittakerSet ψ 0 π, ∃ W₂ ∈ inverseWhittakerSet ψ 0 σ,
      ∃ Φ : SchwartzBruhat (Fin 1 → K.Carrier), ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        EqualRankConverges ψ abv μ W₁ W₂ Φ s ∧
        equalRankIntegral ψ abv μ W₁ W₂ Φ s = (P.eval (spectralPoint qK s))⁻¹

private theorem exists_rankOneCharacterTests (ψ : UnitaryAdditiveCharacter K.Carrier)
    (χ η : Quasicharacter K.Carrier) :
    ∃ W₁ ∈ whittakerSet ψ 0 (rankOneCharacter (χ : K.Carrierˣ →* ℂˣ)),
      ∃ W₂ ∈ inverseWhittakerSet ψ 0 (rankOneCharacter (η : K.Carrierˣ →* ℂˣ)),
        ∀ g, W₁.val g * W₂.val g = ((χ * η : Quasicharacter K.Carrier) (determinant g) : ℂ) := by
  let π := rankOneCharacter (χ : K.Carrierˣ →* ℂˣ)
  let σ := rankOneCharacter (η : K.Carrierˣ →* ℂˣ)
  let ℓ : glFunctionals ψ 0 π := ⟨LinearMap.id, by rw [glFunctionals_rankOne]; trivial⟩
  let ℓ' : glInverseFunctionals ψ 0 σ :=
    ⟨LinearMap.id, by rw [glInverseFunctionals_rankOne]; trivial⟩
  refine ⟨coefficientMap π ℓ 1, ⟨ℓ, 1, rfl⟩,
    coefficientMap σ ℓ' 1, ⟨ℓ', 1, rfl⟩, fun g => ?_⟩
  change ((χ (determinant g) : ℂ) * 1) * ((η (determinant g) : ℂ) * 1) = _
  rw [mul_one, mul_one]
  rfl

/-- Tate's scalar normalizing test transports to the actual ordinary JPSS integral. -/
theorem padicRankOneOrdinaryTest : PadicRankOneOrdinaryTestStatement.{u, uV, uW} K := by
  intro V W _ _ _ _ ψ ν π σ P hπa hπi hσa hσi hP
  obtain ⟨χ, ⟨e⟩⟩ := exists_tateCharacterModel π hπa hπi
  obtain ⟨η, ⟨e'⟩⟩ := exists_tateCharacterModel σ hσa hσi
  have hL := GodementJacquet.Padic.rankOneCharacters_isPadicPairLPolynomial K χ ψ η ν
  have hPeq := ((IsPadicPairLPolynomial.congr_equiv e e').mp hP).unique hL
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := exists_rankOneCharacterTests K ψ χ η
  rw [← whittakerSet_eq_of_equiv ψ e] at hW₁
  rw [← inverseWhittakerSet_eq_of_equiv ψ e'] at hW₂
  let T := K.canonicalTopologicalData
  obtain ⟨φ, b, hb⟩ := rationalLFactor_mem_scalarMellinRationalValues K T (χ * η)
  obtain ⟨a, ha⟩ := (GodementJacquet.Padic.tateCharacter_mellinAnalyticData K (χ * η)).1
  obtain ⟨c, hc⟩ := exists_rightHalfPlane_eval_spectralPoint_ne_zero T.residueCardinality_gt_one
    (P := P) (by rw [hPeq, ← Polynomial.coeff_zero_eq_eval_zero, LocalFactor.PadicAbelian.lPolynomial_coeff_zero]
                 exact one_ne_zero)
  let Φ : SchwartzBruhat (Fin 1 → K.Carrier) :=
    Hecke.TestFunction.pullback (Homeomorph.piUnique (fun _ : Fin 1 => K.Carrier)) φ
  have hfun (s : ℂ) :
      (fun x => equalRankFunction ψ abv W₁ W₂ Φ s (tateScalarEquiv K.Carrier x)) =
        scalarMellinIntegrand T.normalizedAbs (fun x => ((χ * η : Quasicharacter K.Carrier) x : ℂ))
          1 φ s := by
    funext x
    have hdet : determinant (tateScalarEquiv K.Carrier x) = x :=
      (tateScalarEquiv K.Carrier).left_inv x
    have hΦ : Φ (lastRow (tateScalarEquiv K.Carrier x)) = φ (x : K.Carrier) := by
      change φ ((scalar x : Langlands.GeneralLinear 1 K.Carrier).val 0 0) = φ (x : K.Carrier)
      simp [scalar]
    rw [equalRankFunction, hW, hdet, hΦ]
    change ((χ * η : Quasicharacter K.Carrier) x : ℂ) * φ (x : K.Carrier) *
      (T.normalizedAbs (determinant (tateScalarEquiv K.Carrier x) : K.Carrier) : ℂ) ^ s = _
    rw [hdet]
    simp only [scalarMellinIntegrand, Nat.cast_one, one_mul, mul_comm (φ (x : K.Carrier))]
  have hμ := eq_rankOneQuotientHaar_of_isCompatible K.Carrier μ
    (unipotentQuotientHaar_isCompatible K.Carrier 0)
  refine ⟨W₁, hW₁, W₂, hW₂, Φ, max a (max b c), fun s hs => ?_⟩
  have hsa := (le_max_left _ _).trans_lt hs
  have hsb := (le_max_left b c).trans_lt ((le_max_right a _).trans_lt hs)
  have hsc := (le_max_right b c).trans_lt ((le_max_right a _).trans_lt hs)
  rw [hμ, equalRankConverges_rankOneQuotientHaar_iff, equalRankIntegral_rankOneQuotientHaar]
  constructor
  · apply (GodementJacquet.Padic.integrable_tateScalarEquiv_iff K _).mp
    rw [hfun]
    exact ha φ s hsa
  · rw [← GodementJacquet.Padic.integral_tateScalarEquiv K, hfun]
    change scalarMellinIntegral T.normalizedAbs (localMultiplicativeHaar K.Carrier)
      (fun x => ((χ * η : Quasicharacter K.Carrier) x : ℂ)) 1 φ s = _
    rw [(hb s hsb).2]
    have he := (regular_and_eval_div (spectralPoint qK s) 1 P (hc s hsc)).2
    rw [hPeq] at he
    simpa only [LocalFactor.PadicAbelian.rationalLFactor, map_one, one_div, Polynomial.eval_one,
      hPeq] using he

end Langlands.RankinSelberg
