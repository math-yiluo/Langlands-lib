import Langlands.Global.Factors.CertifiedFactorSeparationStatement
import Langlands.Global.Factors.SeparationProof

noncomputable section

namespace Langlands.Global.FactorSeparation

universe uF uP uA uE

open Correspondence LocalFactor LocalFactor.CommonClosure Weil.Local Polynomial

private theorem epsilon_data_eq {a c : ℂˣ} {m k : ℤ}
    (h : (RankinSelberg.rationalEpsilonMonomial a m : RatFunc ℂ) =
      (RankinSelberg.rationalEpsilonMonomial c k : RatFunc ℂ)) :
    a = c ∧ m = k := by
  apply RankinSelberg.unitMonomial_eq_of_infinite
    (Set.finite_singleton (0 : ℂ)).infinite_compl
  · intro z hz
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
  · intro z hz
    have hz0 : z ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    have he := congrArg (RatFunc.eval (RingHom.id ℂ) z) h
    simpa only [RankinSelberg.eval_rationalEpsilonMonomial _ _ hz0] using he

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private theorem residue_reflectedVariable :
    RationalReflection.reflectedVariable (residueReflection F) =
      (RatFunc.C (F.canonicalTopologicalData.residueCardinality : ℂ))⁻¹ *
        (RatFunc.X : RatFunc ℂ)⁻¹ := by
  simp only [RationalReflection.reflectedVariable, coe_residueReflection,
    div_eq_mul_inv, map_inv₀, RatFunc.algebraMap_eq_C]

/-- Conditional application of the four-polynomial separation target to the
existing actual pair-factor certificates. -/
theorem certifiedFactorSeparation_of_separation
    (hsep : GammaSeparationStatement) :
    CertifiedFactorSeparationStatement.{uF, uP, uA, uE} F := by
  intro eC ε hε ψ X Y A hA r t π π' hW hGL hcommon
  refine ⟨hcommon.1, ?_⟩
  intro ν hν
  obtain ⟨G, hGA, hGW⟩ := hcommon.2 ν hν
  obtain ⟨πd, πd', Q, Qd, e, hπd, hπd', hQ, hQd, he, hGa⟩ := hGA
  obtain ⟨a, m, ha, hGw⟩ := hGW
  let P := WeilDeligne.eulerPolynomial A (localInertia F) (localGeometricFrobenius F)
  let Pd := WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A)
    (localInertia F) (localGeometricFrobenius F)
  have hP0 : P.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using
      WeilDeligne.eulerPolynomial_coeff_zero A (localInertia F) (localGeometricFrobenius F)
  have hPd0 : Pd.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using
      WeilDeligne.eulerPolynomial_coeff_zero (WeilDeligneRepresentation.dual A)
        (localInertia F) (localGeometricFrobenius F)
  have hQ0 : Q.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hQ.coeff_zero
  have hQd0 : Qd.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hQd.coeff_zero
  have hratio :
      WeilDeligne.rationalLRatioClass (localInertia F) (localGeometricFrobenius F)
        (residueReflection F) (WeilDeligneRepresentation.tensorClass X Y) =
      algebraMap ℂ[X] (RatFunc ℂ) P /
        aeval (RationalReflection.reflectedVariable (residueReflection F)) Pd := by
    rw [← hA, WeilDeligne.rationalLRatioClass_classOf, WeilDeligne.rationalLRatio_eq]
  have hgam := hGw.symm.trans hGa
  rw [hratio, RankinSelberg.rationalGammaExpression] at hgam
  have hGL' := hGL ν hν πd πd' Q Qd hπd hπd' hQ hQd
  have hs := hsep.1 F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one P Pd Q Qd a e.1 m e.2
    hP0 hPd0 hQ0 hQd0 hW hGL'
  obtain ⟨hPQ, hPdQd, heps⟩ := hs (by
    simpa only [RankinSelberg.coe_rationalEpsilonMonomial, RatFunc.algebraMap_eq_C,
      RatFunc.aeval_X_left_eq_algebraMap, ← residue_reflectedVariable F,
      mul_div_assoc] using hgam)
  have heps' : (RankinSelberg.rationalEpsilonMonomial a m : RatFunc ℂ) =
      (RankinSelberg.rationalEpsilonMonomial e.1 e.2 : RatFunc ℂ) := by
    simpa only [RankinSelberg.coe_rationalEpsilonMonomial, RatFunc.algebraMap_eq_C] using heps
  obtain ⟨hc, hm⟩ := epsilon_data_eq heps'
  have ha' : IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y e.1 e.2 := by
    simpa only [hc, hm] using ha
  refine ⟨πd, πd', Q, Qd, e, hπd, hπd', hQ, hQd, he, ha',
    hPQ.symm, hPdQd.symm, ?_, ?_⟩
  · unfold arithmeticPairLFactor WeilDeligne.pairLFactorClass
    rw [← hA, WeilDeligne.rationalLFactorClass_classOf]
    change (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ = _
    rw [hPQ]
  · change (algebraMap ℂ[X] (RatFunc ℂ) Pd)⁻¹ = _
    rw [hPdQd]

/-- Apply the published algebraic separation theorem to the actual arithmetic
and automorphic certificates, retaining the target's analytic hypotheses. -/
theorem certifiedFactorSeparation :
    CertifiedFactorSeparationStatement.{uF, uP, uA, uE} F :=
  certifiedFactorSeparation_of_separation F Langlands.Global.gammaSeparation

end Langlands.Global.FactorSeparation
