import Langlands.LocalFactor.UnitaryArithmeticPair
import Langlands.LocalFactor.UnitaryGamma
import Langlands.Correspondence.SupercuspidalGammaCompatibility

/-! # Unitary arithmetic gamma orders from the actual rational factor formula -/

noncomputable section

open Filter
open scoped Topology

universe uG uV uF uP u

namespace Langlands.LocalFactor

/-- Evaluation of the original rational function at the published spectral point. -/
def rationalSpectralValue (q : ℕ) (R : RatFunc ℂ) : ℂ → ℂ :=
  fun s => R.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s)

theorem epsilonMonomial_analyticAt (q : ℕ) (hq : 0 < (q : ℝ))
    (c : ℂˣ) (m : ℤ) (s : ℂ) :
    AnalyticAt ℂ (RankinSelberg.epsilonMonomial q c m) s := by
  have he : AnalyticAt ℂ
      (fun z : ℂ => Complex.exp (-z * (Real.log (q : ℝ) : ℂ))) s :=
    (analyticAt_id.neg.mul analyticAt_const).cexp
  unfold RankinSelberg.epsilonMonomial
  simp_rw [RankinSelberg.spectralPoint_eq_spectralParameter q hq]
  change AnalyticAt ℂ
    (fun z : ℂ => (c : ℂ) * Complex.exp (-z * (Real.log (q : ℝ) : ℂ)) ^ m) s
  exact analyticAt_const.mul (he.zpow (Complex.exp_ne_zero _))

namespace WeilDeligne

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- Rational evaluation and the determinant expression have the same punctured
germ, including at a displayed pole and at a cancelled singularity. -/
theorem rationalSpectralValue_eventuallyEq_spectralGammaExpression
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary)
    (g : G) (q : ℕ) (hq : 1 < q) (c : ℂˣ) (m : ℤ) (s : ℂ) :
    rationalSpectralValue q
        ((RankinSelberg.rationalEpsilonMonomial c m : RatFunc ℂ) *
          rationalLRatio A I g
            (reflectionScale (q : ℝ) (by exact_mod_cast (show 0 < q by omega)))) =ᶠ[𝓝[≠] s]
      spectralGammaExpression A I g (q : ℝ)
        (by exact_mod_cast (show 0 < q by omega))
        (RankinSelberg.epsilonMonomial q c m) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast hq
  have hd := FiniteRepresentation.isUnitary_dual A.toFiniteRepresentation hA
  let D : ReciprocalEntire := {
    denominator := fun z =>
      spectralDenominator (kernelOperator (WeilDeligneRepresentation.dual A) I g)
        (q : ℝ) hq0 (1 - z)
    entire := fun z =>
      ((analyticAt_spectralDenominator _ _ _ (1 - z)).comp
        (analyticAt_const.sub analyticAt_id)).differentiableAt
    nonzero := ⟨0, by
      simpa only [sub_zero, spectralDenominator, eulerPolynomial] using
        eulerPolynomial_spectral_eval_ne_zero_of_isUnitary
          (WeilDeligneRepresentation.dual A) I hd g
          (q := (q : ℝ)) hq1 (s := 1) (by simp)⟩ }
  filter_upwards [D.denominator_eventually_ne_zero s] with z hz
  have href :
      (eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
        ((reflectionScale (q : ℝ) hq0 : ℂ) / RankinSelberg.spectralPoint q z) ≠ 0 := by
    rw [coe_reflectionScale, Complex.ofReal_natCast,
      ← RankinSelberg.spectralPoint_one_sub hq z,
      RankinSelberg.spectralPoint_eq_spectralParameter q hq0]
    exact hz
  have heval := RankinSelberg.eval_rationalGammaExpression
    (reflectionScale (q : ℝ) hq0) c m (eulerPolynomial A I g)
      (eulerPolynomial (WeilDeligneRepresentation.dual A) I g)
      (RankinSelberg.spectralPoint_ne_zero hq z) href
  rw [coe_reflectionScale, Complex.ofReal_natCast,
    ← RankinSelberg.spectralPoint_one_sub hq z] at heval
  rw [rationalSpectralValue, rationalLRatio_eq, ← mul_div_assoc]
  change RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q z)
    (RankinSelberg.rationalGammaExpression _ c m _ _) = _
  simpa only [spectralGammaExpression, operatorSpectralGamma, spectralDenominator,
    RankinSelberg.epsilonMonomial, RankinSelberg.spectralPoint_eq_spectralParameter q hq0,
    eulerPolynomial] using heval

/-- The actual rational gamma expression has nonpositive order off the
imaginary axis whenever its original Weil action is unitary. -/
theorem rationalSpectralValue_gamma_order_nonpos
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary)
    (g : G) (q : ℕ) (hq : 1 < q) (c : ℂˣ) (m : ℤ) (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (rationalSpectralValue q
        ((RankinSelberg.rationalEpsilonMonomial c m : RatFunc ℂ) *
          rationalLRatio A I g
            (reflectionScale (q : ℝ) (by exact_mod_cast (show 0 < q by omega))))) s ≤ 0 := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast hq
  rw [meromorphicOrderAt_congr
    (rationalSpectralValue_eventuallyEq_spectralGammaExpression A I hA g q hq c m s)]
  exact spectralGammaExpression_order_nonpos A I hA g q hq1
    (RankinSelberg.epsilonMonomial q c m) s (epsilonMonomial_analyticAt q hq0 c m s)
    (RankinSelberg.epsilonMonomial_ne_zero q hq0 c m s) hs

end WeilDeligne
end Langlands.LocalFactor

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The supplied arithmetic pair gamma relation already provides the analytic
unit epsilon monomial. Thus no separate epsilon analyticity input is needed. -/
theorem IsArithmeticPairGammaFactor.order_nonpos_of_isUnitary
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uV} F}
    {hε : NonabelianSystem.IsSystem F eC ε} {ψ : NontrivialAdditiveCharacter F}
    {A B : LocalWeilDeligneRepresentation.{uF, uP} F} {R : RatFunc ℂ}
    (hR : IsArithmeticPairGammaFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf A) (WeilDeligneRepresentation.classOf B) R)
    (hA : A.toFiniteRepresentation.IsUnitary) (hB : B.toFiniteRepresentation.IsUnitary)
    (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality R) s ≤ 0 := by
  obtain ⟨c, m, _, hR⟩ := hR
  change R = (RankinSelberg.rationalEpsilonMonomial c m : RatFunc ℂ) *
    WeilDeligne.rationalLRatio (WeilDeligneRepresentation.tensor A B)
      (localInertia F) (localGeometricFrobenius F) (residueReflection F) at hR
  rw [hR]
  exact WeilDeligne.rationalSpectralValue_gamma_order_nonpos
    (WeilDeligneRepresentation.tensor A B) (localInertia F)
    (WeilDeligneRepresentation.tensor_isUnitary hA hB) (localGeometricFrobenius F)
    F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one c m s hs

end Langlands.Correspondence

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open LocalFactor LocalFactor.CommonClosure

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- The actual arithmetic self-pair factor of a unitary relative Weil
representation has nonpositive order off the imaginary axis. -/
theorem localSelfPairGamma_order_nonpos
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uP} (padicField v)}
    {hε : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)}
    {R : RatFunc ℂ}
    (hR : Correspondence.IsArithmeticPairGammaFactor (padicField v) eC ε hε ψ
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι) R)
    (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (rationalSpectralValue (padicField v).canonicalTopologicalData.residueCardinality R)
      s ≤ 0 :=
  hR.order_nonpos_of_isUnitary
    (localComponent_isUnitary ι hS)
    (localComponent_isUnitary ι (FiniteRepresentation.isUnitary_dual S hS)) s hs

/-- On the real axis, a positive order of the actual arithmetic self-pair
factor can occur only at zero. -/
theorem localSelfPairGamma_real_positive_order_only_zero
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uP} (padicField v)}
    {hε : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)}
    {R : RatFunc ℂ}
    (hR : Correspondence.IsArithmeticPairGammaFactor (padicField v) eC ε hε ψ
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι) R)
    (t : ℝ)
    (ht : 0 < meromorphicOrderAt
      (rationalSpectralValue (padicField v).canonicalTopologicalData.residueCardinality R)
      (t : ℂ)) :
    t = 0 := by
  by_contra ht0
  exact (not_lt_of_ge
    (localSelfPairGamma_order_nonpos ι hS hR t (by simpa using ht0))) ht

end Langlands.ClassField.Global.RelativeWeilGroup
