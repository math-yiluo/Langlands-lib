import Langlands.Correspondence.BaseLocalEuler
import Langlands.Correspondence.RankOneSpectralEpsilon
import Langlands.LocalFactor.Abelian.GaussDual
import Langlands.LocalFactor.Abelian.Laurent
import Langlands.LocalFactor.Harmonic.DualityProof
import Langlands.Weil.Local.AssemblyProof

/-! # Constructed rank-one arithmetic epsilon data at the actual self-dual measure -/

noncomputable section

universe uF uP uV

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
open Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance arithmeticEpsilonDataTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance arithmeticEpsilonDataMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance arithmeticEpsilonDataBottomAlgebra : Algebra (Padic p) (baseExtension F).field :=
  ((baseExtension F).asPadicField (p := p)).algebra

/-- Every actual nontrivial additive character admits exactly one actual regular
Haar measure with the existing intrinsic Fourier self-duality property. -/
theorem existsUnique_localSelfDualMeasure (ψ : NontrivialAdditiveCharacter F) :
    ∃! μ : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ μ := by
  let T := F.canonicalTopologicalData
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let : BorelSpace F.Carrier := ⟨rfl⟩
  obtain ⟨htd, hdual⟩ := LocalFactors.padicFourierDuality p F T
  let := htd
  have hd := hdual ψ.toAddChar ψ.continuous_toFun ψ.nontrivial
  obtain ⟨μ, hμ⟩ := hd.2.1
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact hd.2.2.1 ν μ hν hμ

/-- The actual self-dual measure, chosen only from proved existence and uniqueness. -/
def localSelfDualHaar (ψ : NontrivialAdditiveCharacter F) : LocalAdditiveHaarMeasure F :=
  (existsUnique_localSelfDualMeasure F ψ).exists.choose

theorem isSelfDual_localSelfDualHaar (ψ : NontrivialAdditiveCharacter F) :
    IsSelfDualMeasure F ψ (localSelfDualHaar F ψ) :=
  (existsUnique_localSelfDualMeasure F ψ).exists.choose_spec

theorem eq_localSelfDualHaar (ψ : NontrivialAdditiveCharacter F)
    (μ : LocalAdditiveHaarMeasure F) (hμ : IsSelfDualMeasure F ψ μ) :
    μ = localSelfDualHaar F ψ :=
  (existsUnique_localSelfDualMeasure F ψ).unique hμ (isSelfDual_localSelfDualHaar F ψ)

/-- The constructed actual spectral abelian epsilon expression is nonzero
at every complex parameter and every supplied actual Haar measure. -/
theorem abelianSpectralEpsilon_ne_zero (χ : QuasiCharacter F)
    (ψ : NontrivialAdditiveCharacter F) (μ : LocalAdditiveHaarMeasure F) (s : ℂ) :
    PadicAbelian.epsilon F.canonicalTopologicalData χ ψ μ.measure s ≠ 0 := by
  let T := F.canonicalTopologicalData
  exact PadicAbelian.epsilonAt_ne_zero T (PadicAbelian.uniformizerUnit T) χ
    ((PadicAbelian.conductorAt_iff T χ _).2 rfl) ψ (T.additiveConductor ψ) μ
    ((PadicAbelian.additiveConductorAt_iff T ψ _).2 rfl) s

/-- The actual nonzero Gauss coefficient at the unique self-dual measure. -/
def rankOneArithmeticEpsilonCoefficient (ψ : NontrivialAdditiveCharacter F)
    (χ : QuasiCharacter F) : ℂˣ :=
  Units.mk0
    (PadicAbelian.deligneConstant F.canonicalTopologicalData χ ψ
      (localSelfDualHaar F ψ).measure)
    (abelianSpectralEpsilon_ne_zero F χ ψ (localSelfDualHaar F ψ) 0)

private theorem abelianSpectralVariable_eq (s : ℂ) :
    PadicAbelian.spectralVariable F.canonicalTopologicalData s =
      RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s := by
  symm
  rw [RankinSelberg.spectralPoint, Complex.cpow_def_of_ne_zero
    (by exact_mod_cast (Nat.zero_lt_one.trans
      F.canonicalTopologicalData.residueCardinality_gt_one).ne')]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log
    (show (0 : ℝ) ≤ (F.canonicalTopologicalData.residueCardinality : ℝ) by positivity)]
  exact congrArg Complex.exp (mul_comm _ _)

/-- Every self-dual measure gives this same actual coefficient and the original
conductor exponent, in the unchanged epsilon-monomial convention. -/
theorem abelianSpectralEpsilon_eq_rankOneMonomial (ψ : NontrivialAdditiveCharacter F)
    (χ : QuasiCharacter F) (μ : LocalAdditiveHaarMeasure F)
    (hμ : IsSelfDualMeasure F ψ μ) (s : ℂ) :
    PadicAbelian.epsilon F.canonicalTopologicalData χ ψ μ.measure s =
      RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality
        (rankOneArithmeticEpsilonCoefficient F ψ χ)
        (PadicAbelian.epsilonExponent F.canonicalTopologicalData χ ψ) s := by
  rw [eq_localSelfDualHaar F ψ μ hμ,
    PadicAbelian.epsilon_eq_constant_mul_spectral_pow, abelianSpectralVariable_eq F s]
  rfl

/-- Constructed full arithmetic rank-one epsilon data for any supplied compatible
reciprocity family and validated local-constant system. -/
theorem isArithmeticPairEpsilonFactor_rankOne_constructed
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (χ η : QuasiCharacter F) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η))
      (rankOneArithmeticEpsilonCoefficient F ψ (χ * η))
      (PadicAbelian.epsilonExponent F.canonicalTopologicalData (χ * η) ψ) := by
  apply (isArithmeticPairEpsilonFactor_rankOne_spectral_iff F e eC h ε hε ψ χ η _ _).2
  refine ⟨⟨localSelfDualHaar F ψ, isSelfDual_localSelfDualHaar F ψ⟩,
    ⟨baseGeometricFrobenius F⟩, ?_⟩
  intro μ hμ s
  exact abelianSpectralEpsilon_eq_rankOneMonomial F ψ (χ * η) μ hμ s

end Langlands.Correspondence
