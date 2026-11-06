import Langlands.LocalFactor.CommonClosureSurjectivity
import Langlands.LocalFactor.CommonClosureSpectralAnalyticStatement
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Rank-one spectral twists of common-closure local constants

The spectral twist of a rank-one class multiplies the abelian epsilon
expression by an exponential in the spectral parameter, so the rank-one
spectral value is entire.
-/

noncomputable section

universe u uF uV

namespace Langlands.LocalFactor.CommonClosureSpectralAnalytic

open MeasureTheory

section Abelian

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} (T : K.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter K.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure K.Carrier _ T.topology
    (@borel K.Carrier T.topology)

/-- `η'` is `η` times the `s`-th power of the normalized absolute value. -/
def IsAbsTwist (η η' : MultiplicativeCharacter) (s : ℂ) : Prop :=
  ∀ u : K.Carrierˣ, (η' u : ℂ) =
    (η u : ℂ) * Complex.exp (s * (Real.log (T.normalizedAbs (u : K.Carrier)) : ℂ))

/-- The exponent of the spectral factor: additive plus multiplicative conductor. -/
def twistExponent (η : MultiplicativeCharacter) (ψ : AdditiveCharacter) : ℤ :=
  T.additiveConductor ψ + (T.multiplicativeConductor η : ℤ)

theorem normalizedAbs_of_value_one {u : K.Carrierˣ}
    (hu : T.discreteValuation (u : K.Carrier) = 1) :
    T.normalizedAbs (u : K.Carrier) = 1 := by
  simp [PadicField.TopologicalData.normalizedAbs, PadicField.TopologicalData.ord, hu]

theorem normalizedAbs_on_valuationShell (k : ℤ) {x : K.Carrier}
    (hx : x ∈ T.valuationShell k) :
    T.normalizedAbs x = (T.residueCardinality : ℝ) ^ k := by
  have hx0 := T.valuationShell_ne_zero k hx
  change T.discreteValuation x = WithZero.exp k at hx
  simp [PadicField.TopologicalData.normalizedAbs, PadicField.TopologicalData.ord, hx0, hx]

theorem multiplicativeConductor_eq_of_isAbsTwist {η η' : MultiplicativeCharacter} {s : ℂ}
    (h : IsAbsTwist T η η' s) :
    T.multiplicativeConductor η' = T.multiplicativeConductor η := by
  have key (n : ℕ) : T.MultiplicativeTrivialAt η' n ↔ T.MultiplicativeTrivialAt η n := by
    have hu : ∀ u ∈ T.principalUnits n, η' u = η u := by
      intro u hu
      apply Units.ext
      rw [h u, normalizedAbs_of_value_one T hu.1]
      simp
    exact forall₂_congr fun u hu' => by rw [hu u hu']
  apply le_antisymm
  · exact (T.multiplicativeTrivialAt_iff_conductor_le η' _).mp
      ((key _).mpr (T.multiplicativeConductor_spec η))
  · exact (T.multiplicativeTrivialAt_iff_conductor_le η _).mp
      ((key _).mp (T.multiplicativeConductor_spec η'))

/-- The abelian epsilon expression of an absolute-value twist, in both the
unramified and the ramified branch. -/
theorem abelianEpsilonExpression_of_isAbsTwist {η η' : MultiplicativeCharacter} {s : ℂ}
    (h : IsAbsTwist T η η' s) (ψ : AdditiveCharacter) (μ : LocalHaar) :
    T.abelianEpsilonExpression η' ψ μ =
      T.abelianEpsilonExpression η ψ μ *
        Complex.exp (-s * ((twistExponent T η ψ : ℂ) *
          (Real.log (T.residueCardinality : ℝ) : ℂ))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace K.Carrier := borel K.Carrier
  have : BorelSpace K.Carrier := ⟨rfl⟩
  have hcond := multiplicativeConductor_eq_of_isAbsTwist T h
  have hexp (k : ℤ) : Complex.exp (s * (Real.log ((T.residueCardinality : ℝ) ^ k) : ℂ)) =
      Complex.exp (s * ((k : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ))) := by
    rw [Real.log_zpow]
    push_cast
    rfl
  unfold PadicField.TopologicalData.abelianEpsilonExpression
  simp only [hcond]
  split_ifs with h0
  · set k := T.additiveConductor ψ + (T.multiplicativeConductor η : ℤ) with hk
    have habs : T.normalizedAbs (T.abelianScale k : K.Carrier) =
        (T.residueCardinality : ℝ) ^ (-k) := by
      rw [PadicField.TopologicalData.normalizedAbs, ite_eq_right (Units.ne_zero _),
        T.abelianScale_order]
    rw [h, habs, hexp]
    have he : Complex.exp (s * (((-k : ℤ) : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ))) =
        Complex.exp (-s * ((twistExponent T η ψ : ℂ) *
          (Real.log (T.residueCardinality : ℝ) : ℂ))) := by
      congr 1
      simp only [twistExponent, ← hk]
      push_cast
      ring
    rw [he]
    ring
  · unfold PadicField.TopologicalData.abelianGaussIntegral
      PadicField.TopologicalData.epsilonShell
    simp only [hcond]
    rw [mul_comm, ← integral_const_mul]
    apply setIntegral_congr_fun (T.valuationShell_compact_closed _).2.measurableSet
    intro x hx
    have hx0 : x ≠ 0 := T.valuationShell_ne_zero _ hx
    have habs := normalizedAbs_on_valuationShell T _ hx
    simp only [HarmonicAnalysis.Quasicharacter.epsilonIntegrand,
      HarmonicAnalysis.Quasicharacter.extendZero, hx0, ↓reduceDIte]
    rw [h, Units.val_mk0, habs, hexp, mul_inv, ← Complex.exp_neg]
    have he : Complex.exp (-(s * ((((T.additiveConductor ψ +
          (T.multiplicativeConductor η : ℤ)) : ℤ) : ℂ) *
          (Real.log (T.residueCardinality : ℝ) : ℂ)))) =
        Complex.exp (-s * ((twistExponent T η ψ : ℂ) *
          (Real.log (T.residueCardinality : ℝ) : ℂ))) := by
      congr 1
      simp only [twistExponent]
      ring
    rw [he]
    ring

/-- The resulting spectral function is entire. -/
theorem analyticAt_const_mul_exp (A B : ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => A * Complex.exp (-z * B)) s :=
  analyticAt_const.mul ((analyticAt_id.neg.mul analyticAt_const).cexp')

end Abelian

open CommonClosure CommonClosureSpectral VirtualRepresentation Weil.Local

section CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (e : ReciprocityFamily F) (E : Extension F)

/-- Descent to the actual topological abelianization followed by transport
through the supplied reciprocity component. -/
def fieldCharacterEquiv : (weilSubgroup F E →ₜ* ℂˣ) ≃ FieldCharacter F E := by
  letI := (fieldData F E).topology
  exact LocalClassField.abelianizationLiftEquiv.trans
    (LocalClassField.characterTransport (e E))

theorem weilCharacter_fieldCharacterEquiv (χ : weilSubgroup F E →ₜ* ℂˣ) :
    weilCharacter F e E (fieldCharacterEquiv F e E χ) = χ :=
  (fieldCharacterEquiv F e E).symm_apply_apply χ

/-- The reciprocity map on the original Weil subgroup is onto, since it is a
quotient projection followed by the supplied equivalence. -/
theorem reciprocityUnits_surjective : Function.Surjective (reciprocityUnits F e E) :=
  Langlands.LocalFactor.CommonClosure.reciprocityUnits_surjective F e E

/-- Geometric normalization identifies the base-degree spectral character with
the absolute-value power on the same intermediate field. -/
theorem character_eq_norm_exp (he : NormalizedReciprocity F e)
    (z : ℂ) (w : weilSubgroup F E) :
    (character F E z w : ℂ) =
      Complex.exp (z * (Real.log ((fieldData F E).normalizedAbs
        (reciprocityUnits F e E w : E.field)) : ℂ)) := by
  let := (fieldData F E).topology
  have hn :
      (fieldData F E).normalizedAbs (reciprocityUnits F e E w : E.field) =
        baseCardinality F ^ (-(localDegree F w.val).toAdd) :=
    he.2 E (LocalClassField.abelianizationProjection (weilSubgroup F E) w)
  rw [character_apply, hn, Real.log_zpow, Complex.ofReal_mul,
    Complex.ofReal_intCast, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- Transporting a spectral product of Weil characters gives an actual
absolute-value twist, with no additional comparison premise. -/
theorem fieldCharacterEquiv_isAbsTwist (he : NormalizedReciprocity F e)
    (χ : weilSubgroup F E →ₜ* ℂˣ) (z : ℂ) :
    IsAbsTwist (fieldData F E) (fieldCharacterEquiv F e E χ)
      (fieldCharacterEquiv F e E (character F E z * χ)) z := by
  let := (fieldData F E).topology
  intro u
  obtain ⟨w, rfl⟩ := reciprocityUnits_surjective F e E u
  change (weilCharacter F e E
      (fieldCharacterEquiv F e E (character F E z * χ)) w : ℂ) =
    (weilCharacter F e E (fieldCharacterEquiv F e E χ) w : ℂ) * _
  rw [weilCharacter_fieldCharacterEquiv, weilCharacter_fieldCharacterEquiv,
    ContinuousMonoidHom.mul_apply, Units.val_mul, character_eq_norm_exp F e E he]
  exact mul_comm _ _

/-- The supplied system agrees with the transported abelian expression on every
continuous character of the original common-closure Weil subgroup. -/
theorem value_characterClass (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (χ : weilSubgroup F E →ₜ* ℂˣ)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    (ε E ψ μ (ExactGrothendieckGroup.characterClass χ) : ℂ) =
      (fieldData F E).abelianEpsilonExpression (fieldCharacterEquiv F e E χ) ψ μ := by
  have hc : characterClass.{uF, uV} F e E (fieldCharacterEquiv F e E χ) =
      ExactGrothendieckGroup.characterClass χ := by
    unfold characterClass
    rw [weilCharacter_fieldCharacterEquiv]
  rw [← hc]
  exact hε.2.2.2.2 E _ ψ μ

/-- The ordinary spectral value of every continuous rank-one Weil class is
analytic at every complex point, for every supplied system and intermediate
field. The field and representation-carrier universes are independent. -/
theorem weilCharacter_analyticAt
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (χ : weilSubgroup F E →ₜ* ℂˣ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ =>
      (ε E ψ μ (virtualTwist F E z (ExactGrothendieckGroup.characterClass χ)) : ℂ)) s := by
  have hv (z : ℂ) :
      (ε E ψ μ (virtualTwist F E z (ExactGrothendieckGroup.characterClass χ)) : ℂ) =
        (fieldData F E).abelianEpsilonExpression (fieldCharacterEquiv F e E χ) ψ μ *
          Complex.exp (-z * ((twistExponent (fieldData F E)
            (fieldCharacterEquiv F e E χ) ψ : ℂ) *
              (Real.log ((fieldData F E).residueCardinality : ℝ) : ℂ))) := by
    change (ε E ψ μ (ExactGrothendieckGroup.continuousTwist
      (character F E z) (ExactGrothendieckGroup.characterClass χ)) : ℂ) = _
    rw [ExactGrothendieckGroup.continuousTwist_characterClass,
      value_characterClass F e E ε hε]
    exact abelianEpsilonExpression_of_isAbsTwist (fieldData F E)
      (fieldCharacterEquiv_isAbsTwist F e E hε.1 χ z) ψ μ
  simp_rw [hv]
  exact analyticAt_const_mul_exp _ _ s

end CommonClosure

end Langlands.LocalFactor.CommonClosureSpectralAnalytic
