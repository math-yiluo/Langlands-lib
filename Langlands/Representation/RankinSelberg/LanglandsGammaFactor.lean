import Langlands.Representation.RankinSelberg.LanglandsLFactor
import Langlands.Representation.RankinSelberg.LanglandsFactors
import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Representation.Category.Contragredient
import Langlands.LocalFactor.ResidueReflection

/-!
# Gamma factors from nongeneric epsilon and L factors

Construct the rational unit epsilon times the reflected contragredient L-factor
divided by the original L-factor. All three existence inputs remain explicit.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Polynomial LocalFactor

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

section Pair

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r t : ℕ}
  (π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
  (σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))

/-- The existing nongeneric L relation for the smooth contragredient pair,
with the inverse additive character used by the analytic dual integrals. -/
def IsLanglandsDualPairLPolynomial (Pdual : ℂ[X]) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  IsLanglandsPairLPolynomial.{uF, uV, uW} F (ψ.scale (-1)) ν
    π.contragredient σ.contragredient Pdual

/-- The nongeneric gamma relation uses the genuine smooth contragredients.
The dual polynomial is read with the inverse character, as in the analytic
functional equation. No character-independence theorem is assumed. -/
def IsLanglandsPairGammaFactor (G : RationalFunctions) : Prop :=
  letI := F.canonicalTopologicalData.topology
  ∃ (e : ℂˣ × ℤ) (P Pdual : ℂ[X]),
    IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e ∧
    IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P ∧
    IsLanglandsDualPairLPolynomial.{uF, uV, uW} F ψ ν π σ Pdual ∧
    G = rationalGammaExpression (residueReflection F) e.1 e.2 P Pdual

/-- The three intrinsic factor-existence obligations needed by the constructor.
Classification and analytic existence are not asserted by this proposition. -/
def LanglandsPairGammaInput : Prop :=
  letI := F.canonicalTopologicalData.topology
  (∃ e, IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e) ∧
  (∃ P, IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P) ∧
  (∃ Pdual, IsLanglandsDualPairLPolynomial.{uF, uV, uW} F ψ ν π σ Pdual)

/-- Assemble actual units from certified factors, using the published rational
reflection homomorphism. This performs no evaluation at a possible pole. -/
def langlandsPairGammaUnit
    (e : {e // IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e})
    (P : {P // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P})
    (Pdual : {Pdual // IsLanglandsDualPairLPolynomial.{uF, uV, uW} F ψ ν π σ Pdual}) : RationalFunctionsˣ :=
  rationalEpsilonMonomial e.val.1 e.val.2 *
    Units.map (RationalReflection.subst (residueReflection F)).toMonoidHom
      (langlandsPairLFactor Pdual) / langlandsPairLFactor P

theorem langlandsPairGammaUnit_eq_expression
    (e : {e // IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e})
    (P : {P // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P})
    (Pdual : {Pdual // IsLanglandsDualPairLPolynomial.{uF, uV, uW} F ψ ν π σ Pdual}) :
    (langlandsPairGammaUnit F ψ ν π σ e P Pdual : RationalFunctions) =
      rationalGammaExpression (residueReflection F) e.val.1 e.val.2
        P.val Pdual.val := by
  unfold IsLanglandsDualPairLPolynomial at Pdual
  simp only [langlandsPairGammaUnit, Units.val_div_eq_div_val, Units.val_mul,
    Units.coe_map]
  change (rationalEpsilonMonomial e.val.1 e.val.2 : RationalFunctions) *
    RationalReflection.subst (residueReflection F)
      (langlandsPairLFactor Pdual : RationalFunctions) /
    (langlandsPairLFactor P : RationalFunctions) = _
  rw [coe_langlandsPairLFactor, coe_langlandsPairLFactor, map_inv₀,
    RationalReflection.subst_polynomial]
  unfold rationalGammaExpression
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- Construct a unit with the nongeneric gamma certificate. Choice is applied
only to the three explicit intrinsic existence proofs. -/
def langlandsPairGammaFactor (h : LanglandsPairGammaInput.{uF, uV, uW} F ψ ν π σ) :
    {G : RationalFunctionsˣ //
      IsLanglandsPairGammaFactor.{uF, uV, uW} F ψ ν π σ (G : RationalFunctions)} := by
  let e : {e // IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e} :=
    ⟨h.1.choose, h.1.choose_spec⟩
  let P : {P // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P} :=
    ⟨h.2.1.choose, h.2.1.choose_spec⟩
  let Pdual : {Pdual // IsLanglandsDualPairLPolynomial.{uF, uV, uW} F ψ ν π σ Pdual} :=
    ⟨h.2.2.choose, h.2.2.choose_spec⟩
  exact ⟨langlandsPairGammaUnit F ψ ν π σ e P Pdual,
    e.val, P.val, Pdual.val, e.property, P.property, Pdual.property,
    langlandsPairGammaUnit_eq_expression F ψ ν π σ e P Pdual⟩

variable {F ψ ν π σ}

/-- Uniqueness follows from the existing epsilon and L uniqueness theorems. -/
theorem IsLanglandsPairGammaFactor.unique {G G' : RationalFunctions}
    (h : IsLanglandsPairGammaFactor.{uF, uV, uW} F ψ ν π σ G)
    (h' : IsLanglandsPairGammaFactor.{uF, uV, uW} F ψ ν π σ G') : G = G' := by
  obtain ⟨e, P, Pd, he, hP, hPd, rfl⟩ := h
  obtain ⟨e', P', Pd', he', hP', hPd', rfl⟩ := h'
  rw [he.unique he', hP.unique hP', IsLanglandsPairLPolynomial.unique hPd hPd']

/-- The constructed unit is independent of all chosen factor witnesses. -/
theorem langlandsPairGammaFactor_independent
    (h h' : LanglandsPairGammaInput.{uF, uV, uW} F ψ ν π σ) :
    (langlandsPairGammaFactor F ψ ν π σ h).val =
      (langlandsPairGammaFactor F ψ ν π σ h').val := by
  apply Units.ext
  exact (langlandsPairGammaFactor F ψ ν π σ h).property.unique
    (langlandsPairGammaFactor F ψ ν π σ h').property

/-- Every certified value is the value of the constructed unit and is nonzero. -/
theorem IsLanglandsPairGammaFactor.ne_zero {G : RationalFunctions}
    (h : IsLanglandsPairGammaFactor.{uF, uV, uW} F ψ ν π σ G) : G ≠ 0 := by
  obtain ⟨e, P, Pd, he, hP, hPd, hG⟩ := h
  rw [hG, ← langlandsPairGammaUnit_eq_expression F ψ ν π σ
    ⟨e, he⟩ ⟨P, hP⟩ ⟨Pd, hPd⟩]
  exact Units.ne_zero _

/-- The rational gamma value on the displayed polynomial domain. -/
theorem langlandsPairGammaUnit_eval
    (e : {e // IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e})
    (P : {P // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P})
    (Pdual : {Pdual // IsLanglandsDualPairLPolynomial.{uF, uV, uW} F ψ ν π σ Pdual})
    (s : ℂ)
    (hPd : Pdual.val.eval
      (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ)
      (spectralPoint F.canonicalTopologicalData.residueCardinality s)
      (langlandsPairGammaUnit F ψ ν π σ e P Pdual : RationalFunctions) =
        epsilonMonomial F.canonicalTopologicalData.residueCardinality e.val.1 e.val.2 s *
          P.val.eval (spectralPoint F.canonicalTopologicalData.residueCardinality s) /
          Pdual.val.eval
            (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) := by
  have hq := PadicField.TopologicalData.residueCardinality_gt_one F.canonicalTopologicalData
  have href :
      (residueReflection F : ℂ) /
        spectralPoint F.canonicalTopologicalData.residueCardinality s =
      spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s) := by
    rw [coe_residueReflection, spectralPoint_one_sub hq]
  rw [langlandsPairGammaUnit_eq_expression, eval_rationalGammaExpression
    _ _ _ _ _ (spectralPoint_ne_zero hq s) (by rwa [href]), href]
  rfl

end Pair

end Langlands.RankinSelberg
