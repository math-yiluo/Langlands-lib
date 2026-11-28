import Langlands.Automorphic.AssociatedGammaFinal
import Langlands.BaseChange.CompletedPairDistinguishedPolynomialComparison
import Langlands.BaseChange.CuspidalPairAwayEulerComparison
import Langlands.BaseChange.StandardCompletedPairEquation

/-! # The distinguished Euler product for actual weak base-change pairs -/

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false

universe u uQ uI

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.AdelicFunctoriality Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison Global.FunctionalEquationComparison.RelativeWeilEngine
open LocalClassField LocalFactor.Archimedean
open ClassFieldTheory.Global.RelativeWeilGroup (isCanonicalFiniteAdditiveComponent_unique)
open scoped BigOperators NumberField FiniteExtension

local notation "Γ(" blocks ")" =>
  (fun z : ℂ => (LocalFactor.ReciprocalEntire.denominator (gammaProduct blocks) z)⁻¹)

section Normalization

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r t : ℕ}

set_option maxHeartbeats 1250000 in
private theorem finitePairChoices_eq_at
    {T Td : CuspidalOperatorRealization K r} {T' Td' : CuspidalOperatorRealization K t}
    {P : CuspidalSpectralPresentation.{u,uQ} T} {Pd : CuspidalSpectralPresentation.{u,uQ} Td}
    {P' : CuspidalSpectralPresentation.{u,uQ} T'} {Pd' : CuspidalSpectralPresentation.{u,uQ} Td'}
    {hP : HasIrreducibleAdmissibleComponents P} {hPd : HasIrreducibleAdmissibleComponents Pd}
    {hP' : HasIrreducibleAdmissibleComponents P'} {hPd' : HasIrreducibleAdmissibleComponents Pd'}
    (c d : FinitePairFactorChoice (standardGlobalAdditiveCharacter K) P P' Pd Pd' hP hP' hPd hPd')
    (v : FinitePlace K) :
    c.lPolynomial v = d.lPolynomial v ∧ c.dualLPolynomial v = d.dualLPolynomial v ∧
      c.epsilon v = d.epsilon v := by
  have hc := isCanonicalFiniteAdditiveComponent_unique (c.additive_spec v)
    (isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K v)
  have hd := isCanonicalFiniteAdditiveComponent_unique (d.additive_spec v)
    (isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K v)
  obtain ⟨_, _, hν⟩ := existsUnique_selfDualMeasure_standardFiniteAdditiveComponent K v
  have hψ := hc.trans hd.symm
  have hμ := (hν _ (hc ▸ c.measure_spec v)).trans (hν _ (hd ▸ d.measure_spec v)).symm
  exact ⟨(hψ ▸ hμ ▸ c.lPolynomial_spec v).unique (d.lPolynomial_spec v),
     (hψ ▸ hμ ▸ c.dualLPolynomial_spec v).unique (d.dualLPolynomial_spec v),
     (hψ ▸ hμ ▸ c.epsilon_spec v).unique (d.epsilon_spec v)⟩

set_option maxHeartbeats 4000000 in
private theorem exists_completedEquation_twistedChoice (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u,uQ})
    (D : AutomorphicTwistSetup.{u,uQ} (standardGlobalAdditiveCharacter K) r t) (χ : HeckeCharacter K) :
    ∃ (S : Finset (FinitePlace K)) (A Ad : List GammaBlock) (ε : ℂˣ),
      (∀ v ∉ S, (D.twistedChoice χ).epsilon v = (1, 0)) ∧
      HasGlobalEquation (D.twistedChoice χ).finiteL (D.twistedChoice χ).finiteDualL
        (D.twistedChoice χ).finiteEpsilon Γ(A) Γ(Ad) (fun _ => (ε : ℂ)) S := by
  let c' := D.twistedChoice χ
  have hdu := D.hTd.heckeDeterminantTwist_inv χ
  obtain ⟨c, S, A, Ad, ε, -, -, hε, hEq⟩ := standardCompletedPairEquation hFE K r t
    (D.T.heckeDeterminantTwist χ) (D.Td.heckeDeterminantTwist χ⁻¹) D.T' D.Td' hdu D.hTd'
    (D.P.heckeDeterminantTwist χ) D.P' (D.Pd.heckeDeterminantTwist χ⁻¹) D.Pd'
    (D.P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ D.h) D.h'
    (D.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ D.hd) D.hd'
  have hloc (v : FinitePlace K) := finitePairChoices_eq_at c c' v
  have hL : c.finiteL = c'.finiteL := by
    funext v z
    simp only [FinitePairFactorChoice.finiteL, (hloc v).1]
  have hLd : c.finiteDualL = c'.finiteDualL := by
    funext v z
    simp only [FinitePairFactorChoice.finiteDualL, (hloc v).2.1]
  have hE : c.finiteEpsilon = c'.finiteEpsilon := by
    funext v z
    simp only [FinitePairFactorChoice.finiteEpsilon, (hloc v).2.2]
  rw [hL, hLd, hE] at hEq
  exact ⟨S, A, Ad, ε, fun v hv => (hloc v).2.2.symm.trans (hε v hv), hEq⟩

private theorem twistedChoice_polynomials_eq_of_finiteComponent_eq
    (D : AutomorphicTwistSetup.{u,uQ} (standardGlobalAdditiveCharacter K) r t)
    {χ η : HeckeCharacter K} (v : FinitePlace K) (h : χ.finiteComponent v = η.finiteComponent v) :
    (D.twistedChoice χ).lPolynomial v = (D.twistedChoice η).lPolynomial v ∧
    (D.twistedChoice χ).dualLPolynomial v = (D.twistedChoice η).dualLPolynomial v := by
  simp only [AutomorphicTwistSetup.twistedChoice, AutomorphicTwistSetup.finiteData, h, and_self]

end Normalization

section Comparison

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  {r t : ℕ}
  (D : AutomorphicTwistSetup.{u,uQ} (standardGlobalAdditiveCharacter K) r t)
  (U : AutomorphicTwistSetup.{u,uQ} (standardGlobalAdditiveCharacter L) r t)
  (I : Type uI) [Fintype I] (χ : I → HeckeCharacter K) (v₀ : FinitePlace K) (w₀ : FinitePlacesAbove L v₀)

/-- The distinguished upper pair denominator equals the product of lower
norm-twisted denominators in the common residue variable, given completed
cuspidal equations, weak base change, and distinguished root bounds. -/
def CuspidalPairDistinguishedNormEulerStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u,uQ} →
  U.P.spectralSystem.IsArithmeticWeakBaseChangeOf D.P.spectralSystem →
  U.P'.spectralSystem.IsArithmeticWeakBaseChangeOf D.P'.spectralSystem →
  RelativeWeilEngine.placesAbove L v₀ = {w₀.1} →
  (∀ (v : FinitePlace K) (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
    (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) ∧
    (IsNormTrivial (w.1.adicCompletion L) κ →
      Nat.card {i // ((χ i).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) →
  (∀ i x, ‖x‖ < 1 → ((D.twistedChoice (χ i)).lPolynomial v₀).eval x ≠ 0 ∧
    ((D.twistedChoice (χ i)).dualLPolynomial v₀).eval x ≠ 0) →
  (∀ x, ‖x‖ < 1 → ((U.twistedChoice 1).lPolynomial w₀.1).eval x ≠ 0 ∧
    ((U.twistedChoice 1).dualLPolynomial w₀.1).eval x ≠ 0) →
  ((U.twistedChoice 1).lPolynomial w₀.1).comp (Polynomial.X ^ w₀.1.asIdeal.inertiaDeg (𝓞 K)) =
    ∏ i, (D.twistedChoice (χ i)).lPolynomial v₀

set_option maxHeartbeats 7800000 in
/-- Match the away factors after a common auxiliary twist. Apply the grouped
completed equations and remove the twist at the distinguished places. -/
theorem cuspidalPairDistinguishedNormEuler : CuspidalPairDistinguishedNormEulerStatement D U I χ v₀ w₀ := by
  classical
  intro hFE h₁ h₂ hw₀ hres hroot hroot'
  obtain ⟨μ, -, hμ₀, hμ₀', haway⟩ := cuspidalPairAwayEulerComparison D U I χ v₀ h₁ h₂ hres
  let τ (i : I) := χ i * μ
  let N := μ.normComp (L := L)
  let cF (i : I) := D.twistedChoice (τ i)
  let cE := U.twistedChoice N
  have hτ (i : I) : (τ i).finiteComponent v₀ = (χ i).finiteComponent v₀ := by
    simp only [τ, HeckeCharacter.finiteComponent_mul, hμ₀]
    exact ContinuousMonoidHom.ext fun x => mul_one ((χ i).finiteComponent v₀ x)
  have hN : N.finiteComponent w₀.1 = (1 : HeckeCharacter L).finiteComponent w₀.1 := hμ₀' w₀
  have heq (i : I) := twistedChoice_polynomials_eq_of_finiteComponent_eq D v₀ (hτ i)
  have heq' := twistedChoice_polynomials_eq_of_finiteComponent_eq U w₀.1 hN
  choose SF AF AdF εF hSF hF using fun i => exists_completedEquation_twistedChoice hFE D (τ i)
  obtain ⟨SE, AE, AdE, εE, -, hE⟩ := exists_completedEquation_twistedChoice hFE U N
  let f := w₀.1.asIdeal.inertiaDeg (𝓞 K)
  have hq : residueCardinality w₀.1 = residueCardinality v₀ ^ f := by
    unfold residueCardinality
    rw [canonicalResidueCardinality_eq_absNorm, canonicalResidueCardinality_eq_absNorm]
    exact (Ideal.absNorm_pow_inertiaDeg v₀.asIdeal w₀.1.asIdeal).symm
  have hc := completedPairDistinguishedPolynomialComparison.{u,uQ,uI} K L r t I v₀ w₀.1 f hw₀ hq
    (fun i => D.T.heckeDeterminantTwist (τ i)) (fun i => D.Td.heckeDeterminantTwist (τ i)⁻¹)
    (fun _ => D.T') (fun _ => D.Td') (U.T.heckeDeterminantTwist N) (U.Td.heckeDeterminantTwist N⁻¹) U.T' U.Td'
    (fun i => D.P.heckeDeterminantTwist (τ i)) (fun _ => D.P') (fun i => D.Pd.heckeDeterminantTwist (τ i)⁻¹)
    (fun _ => D.Pd') (U.P.heckeDeterminantTwist N) U.P' (U.Pd.heckeDeterminantTwist N⁻¹) U.Pd'
    (fun i => D.P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (τ i) D.h) (fun _ => D.h')
    (fun i => D.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (τ i)⁻¹ D.hd) (fun _ => D.hd')
    (U.P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents N U.h) U.h'
    (U.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents N⁻¹ U.hd) U.hd'
    cF cE SF SE AF AdF AE AdE εF εE hSF hF hE
    (fun v hv => by simpa only [RelativeWeilEngine.placesAbove, Finset.prod_map, Function.Embedding.coeFn_mk]
      using (haway v hv).1)
    (fun v hv => by simpa only [RelativeWeilEngine.placesAbove, Finset.prod_map, Function.Embedding.coeFn_mk]
      using (haway v hv).2)
    (fun i x hx => by simpa only [cF, (heq i).1, (heq i).2] using hroot i x hx)
    (fun x hx => by simpa only [cE, heq'.1, heq'.2] using hroot' x hx)
  simpa only [cF, cE, heq'.1, fun i => (heq i).1] using hc

end Comparison

end Langlands.BaseChange
