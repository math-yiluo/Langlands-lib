import Langlands.TraceFormula.AdelicFixedLevelSmoothing
import Langlands.TraceFormula.IsotypicTrace.TwistCovariance

/-! # Fixed-level smoothing on the full quotient `L²` space and its cuspidal restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.Global.PositiveRealTorus
open Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis Langlands.Hecke
open Langlands.QuotientIntegration

universe u

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "A" => AdelicGroupPoints F G

private local instance quotientL2FiniteMeasurableSpace : MeasurableSpace Af := borel _
private local instance quotientL2FiniteBorelSpace : BorelSpace Af := ⟨rfl⟩

variable (mInf : Measure (InfiniteAdelicGroupPoints F G)) [mInf.IsHaarMeasure]
  (mFin : Measure (FiniteAdelicGroupPoints F G)) [mFin.IsHaarMeasure]
  (m : Measure (AdelicGroupPoints F G))
  (hProduct : MeasurePreserving (AdelicGroupPoints.split F G).symm (mInf.prod mFin) m)
  {f : InfiniteAdelicGroupPoints F G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
  (Z : CommGroupScheme (Spec (CommRingCat.of F))) (i : Z.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hz : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G Z i
local notation "π" => haarQuotientL2BoundedRightAction F G Z i hi I e hz

/-- The tensor test integrated on the full quotient `L²` space. -/
def quotientL2SmoothingAction (g : HeckeAlgebra mFin) (k : ℕ) : Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ :=
  haarQuotientL2IntegratedAction F G Z i hi I e hz m
    (adelicSmoothingWeight F G mInf f g k)
    (adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hc g k)

set_option backward.isDefEq.respectTransparency false in
/-- Positive powers of the fixed-level smoothing operator on the quotient `L²` space, after a
commuting operator, increase only the infinite convolution power. -/
theorem quotientL2FixedLevelSmoothingPowers (K : OpenSubgroup Af) (hK : IsCompact (K : Set Af))
    (g : HeckeAlgebra mFin) (hg : ∀ k : K, ∀ x, g (x * k) = g x)
    (U : Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ)
    (hU : Commute U (quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz
      (HeckeAlgebra.normalizedIndicator mFin K hK) 0)) (k : ℕ) :
    (quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz g 0 * U) *
        quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz
          (HeckeAlgebra.normalizedIndicator mFin K hK) 0 ^ k =
      quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz g k * U := by
  let R := quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz
  let a := (AdelicGroupPoints.split F G).symm
  have ha : MeasurableEmbedding a := a.toHomeomorph.measurableEmbedding
  let ρ := (π).comp a.toMonoidHom
  let hn := norm_haarQuotientL2BoundedRightAction F G Z i hi I e hz
  let hm := haarQuotientL2Orbit_aestronglyMeasurable F G Z i hi I e hz m
  have hr (g' : HeckeAlgebra mFin) (j : ℕ) :
      smoothingPowerTensorAction mInf mFin ρ (fun x y => hn (a x) y)
        (fun x => (hm x).comp_measurePreserving hProduct) hf hc g' j = R g' j := by
    have hw := adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hc g' j
    have h := integratedIsometricAction_pullback m π hn hm _ hw (mInf.prod mFin) a.toMulEquiv ha
      hProduct
    have hWeight : adelicSmoothingWeight F G mInf f g' j ∘ a.toMulEquiv =
        fun x => positiveConvolutionPower mInf f j x.1 * g' x.2 := by
      funext x
      change adelicSmoothingWeight F G mInf f g' j (AdelicGroupPoints.pair F G x.1 x.2) = _
      simp only [adelicSmoothingWeight, AdelicGroupPoints.infinite_pair,
        AdelicGroupPoints.finite_pair]
    ext1 x
    have hx := congrArg (fun B : Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ => B x) h
    simp only [integratedIsometricAction_apply] at hx
    rw [hWeight] at hx
    exact hx
  have hU' :
      Commute U (smoothingPowerTensorAction mInf mFin ρ (fun x y => hn (a x) y)
        (fun x => (hm x).comp_measurePreserving hProduct) hf hc
        (HeckeAlgebra.normalizedIndicator mFin K hK) 0) := by
    rw [hr]
    exact hU
  simpa only [hr] using fixedLevelSmoothingPowers A∞ Af mInf mFin (Lp ℂ 2 μQ) ρ
    (fun x y => hn (a x) y) (fun x => (hm x).comp_measurePreserving hProduct) f hf hc K hK g hg
    U hU' k

/-- The twisting operator of a measure-preserving automorphism commutes with the quotient
`L²` smoothing action of an invariant tensor test. -/
theorem commute_twistOperator_quotientL2SmoothingAction
    (Θ : A ≃ₜ* A)
    (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G Z i ↔ x ∈ positiveRationalSubgroup F G Z i)
    (hΘμ : MeasurePreserving (quotientAutomorphism (positiveRationalSubgroup F G Z i) Θ hΘ).symm
      μQ μQ)
    (hΘm : MeasurePreserving Θ m m) (g : HeckeAlgebra mFin) (k : ℕ)
    (hInv : ∀ a, adelicSmoothingWeight F G mInf f g k (Θ a) =
      adelicSmoothingWeight F G mInf f g k a) :
    Commute (twistOperator (positiveRationalSubgroup F G Z i) Θ hΘ μQ hΘμ)
      (quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz g k) :=
  commute_integratedIsometricAction_of_invariant m π
    (norm_haarQuotientL2BoundedRightAction F G Z i hi I e hz)
    (haarQuotientL2Orbit_aestronglyMeasurable F G Z i hi I e hz m) _
    (adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hc g k) Θ.toMulEquiv
    Θ.toHomeomorph.measurableEmbedding hΘm _
    (fun a φ => IsotypicTrace.twistOperator_quotientL2RightTranslate F G Z i μQ
      (haarQuotientMeasureRightInvariant F G Z i hi I e hz) Θ hΘ hΘμ a φ) hInv

section Cuspidal

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)

local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hz

/-- The cuspidal smoothing action is the restriction of the quotient `L²` smoothing action. -/
theorem subtypeL_comp_adelicSmoothingAction (g : HeckeAlgebra mFin) (k : ℕ) :
    (S).subtypeL ∘L adelicSmoothingAction F G mInf mFin m hProduct hf hc hPD hG Z i hi I e hz g k =
      quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz g k ∘L
        (S).subtypeL := by
  ext1 φ
  have hint := fullAEL2CuspidalActionIntegrand_integrable F G hPD hG Z i hi I e hz m
    (adelicSmoothingWeight F G mInf f g k)
    (adelicSmoothingWeight_integrable F G mInf mFin m hProduct hf hc g k) φ
  change (S).subtypeL (∫ a, adelicSmoothingWeight F G mInf f g k a •
      fullAEL2CuspidalRightAction F G hPD hG Z i hi I e hz a φ ∂m) =
    ∫ a, adelicSmoothingWeight F G mInf f g k a •
      quotientL2RightAction F G Z i μQ (haarQuotientMeasureRightInvariant F G Z i hi I e hz) a
        ((S).subtypeL φ) ∂m
  rw [← (S).subtypeL.integral_comp_comm hint]
  rfl

/-- Powers of the cuspidal smoothing action are restrictions of the quotient `L²` powers. -/
theorem subtypeL_comp_adelicSmoothingAction_pow (g : HeckeAlgebra mFin) (k j : ℕ) :
    (S).subtypeL ∘L
        (adelicSmoothingAction F G mInf mFin m hProduct hf hc hPD hG Z i hi I e hz g k ^ j) =
      (quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz g k ^ j) ∘L
        (S).subtypeL := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.comp_assoc, ih, ContinuousLinearMap.comp_assoc,
      subtypeL_comp_adelicSmoothingAction, ← ContinuousLinearMap.comp_assoc]

end Cuspidal

/-- Fixed-level smoothing on the full quotient `L²` space: positive powers after a commuting
operator increase only the infinite convolution power; a measure-preserving twist commutes
with the smoothing action of an invariant tensor test; and the cuspidal smoothing action and its
powers are the restrictions of the quotient `L²` ones. -/
def QuotientL2FixedLevelSmoothingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (mInf : Measure (InfiniteAdelicGroupPoints F G)) [mInf.IsHaarMeasure]
    (mFin : Measure (FiniteAdelicGroupPoints F G)) [mFin.IsHaarMeasure]
    (m : Measure (AdelicGroupPoints F G))
    (hProduct : MeasurePreserving (AdelicGroupPoints.split F G).symm (mInf.prod mFin) m)
    (f : InfiniteAdelicGroupPoints F G → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (Z : CommGroupScheme (Spec (CommRingCat.of F))) (i : Z.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hz : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (K : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (hK : IsCompact (K : Set (FiniteAdelicGroupPoints F G))) (g : HeckeAlgebra mFin),
    let R := quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz
    let T := R (HeckeAlgebra.normalizedIndicator mFin K hK) 0
    ((∀ k : K, ∀ x, g (x * k) = g x) →
      ∀ U : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G Z i) →L[ℂ]
        Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G Z i),
        Commute U T → ∀ k : ℕ, (R g 0 * U) * T ^ k = R g k * U) ∧
    (∀ (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G)
      (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G Z i ↔ x ∈ positiveRationalSubgroup F G Z i)
      (hΘμ : MeasurePreserving
        (quotientAutomorphism (positiveRationalSubgroup F G Z i) Θ hΘ).symm
        (positiveRationalQuotientHaarMeasure F G Z i) (positiveRationalQuotientHaarMeasure F G Z i)),
      MeasurePreserving Θ m m → ∀ k : ℕ,
      (∀ a, adelicSmoothingWeight F G mInf f g k (Θ a) = adelicSmoothingWeight F G mInf f g k a) →
      Commute (twistOperator (positiveRationalSubgroup F G Z i) Θ hΘ
        (positiveRationalQuotientHaarMeasure F G Z i) hΘμ) (R g k)) ∧
    ∀ (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G) (k j : ℕ),
      (fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hz).subtypeL ∘L
          (adelicSmoothingAction F G mInf mFin m hProduct hf hc hPD hG Z i hi I e hz g k ^ j) =
        (R g k ^ j) ∘L (fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hz).subtypeL

set_option backward.isDefEq.respectTransparency false in
theorem quotientL2FixedLevelSmoothing : QuotientL2FixedLevelSmoothingStatement.{u} := by
  intro F _ _ G _ _ mInf _ mFin _ m hProduct f hf hc Z i hi _ I _ e hz _ K hK g R T
  exact ⟨fun hg U hU k =>
      quotientL2FixedLevelSmoothingPowers F G mInf mFin m hProduct hf hc Z i hi I e hz K hK g hg U
        hU k,
    fun Θ hΘ hΘμ hΘm k hInv =>
      commute_twistOperator_quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz
        Θ hΘ hΘμ hΘm g k hInv,
    fun hPD hG k j =>
      subtypeL_comp_adelicSmoothingAction_pow F G mInf mFin m hProduct hf hc Z i hi I e hz hPD hG
        g k j⟩

end Langlands.TraceFormula
