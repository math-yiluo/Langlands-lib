import Langlands.Automorphic.AssociatedGammaAutomorphicFamily
import Langlands.Automorphic.AssociatedGammaOutsideMatch
import Langlands.Automorphic.Unramified.WeakInductionNormTwist
import Langlands.Correspondence.SphericalPairTwistLPolynomial
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.Factors.NumberFieldEquationGrouping
import Langlands.Global.RankinSelberg.EqualEulerPointwise
import Langlands.Representation.RankinSelberg.HighlyRamified.ShellExpansion

/-! # Pair L-factor comparison under norm twists at spherical places -/

noncomputable section

set_option autoImplicit false

universe uF uE uV uW uI

namespace Langlands.Global.CuspidalPairFunctionalEquation

open Langlands.Automorphic Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.Global.AdelicFunctoriality
open Langlands.RankinSelberg Polynomial
open scoped NumberField Classical

section LocalFactors

variable {F : Type uF} [Field F] [NumberField F]

private theorem valuation_eq_one_of_integralUnit {v : FinitePlace F}
    {a : (FiniteCompletion F v)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units) :
    Valued.v (a : FiniteCompletion F v) = 1 := by
  have h₁ : Valued.v (a : FiniteCompletion F v) ≤ 1 := ha.1
  have h₂ : Valued.v ((a⁻¹ : (FiniteCompletion F v)ˣ) : FiniteCompletion F v) ≤ 1 := ha.2
  have hpos : 0 < Valued.v (a : FiniteCompletion F v) := by
    apply pos_iff_ne_zero.mpr
    rw [Valuation.ne_zero_iff]
    exact a.ne_zero
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ hpos] at h₂
  exact h₁.antisymm h₂

/-- Vanishing of the transported local conductor is the Hecke unramified condition. -/
theorem conductor_quasicharacterBase_eq_zero_iff (χ : HeckeCharacter F) (v : FinitePlace F) :
    (padicField v).canonicalTopologicalData.multiplicativeConductor
      (quasicharacterBase v (χ.finiteComponent v)) = 0 ↔ χ.IsUnramifiedAt v := by
  rw [PadicField.TopologicalData.multiplicativeConductor_eq_zero_iff]
  refine ⟨fun h a ha => h a ?_, fun h => ?_⟩
  · rw [← topologicalData_eq_canonicalTopologicalData v, FiniteExtension.topologicalData_discreteValuation]
    exact valuation_eq_one_of_integralUnit ha
  · exact (Correspondence.isUnramifiedQuasicharacter_iff_isUnramifiedCharacter _ _).mpr
      (isUnramifiedCharacter_quasicharacterBase χ h)

variable [CompactSpace (AdeleQuotient F)]

private theorem spherical_twistedPair_lPolynomial {r t : ℕ}
    {T : CuspidalOperatorRealization F r} {U : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{uF,uV} T) (R : CuspidalSpectralPresentation.{uF,uV} U)
    (hP : HasIrreducibleAdmissibleComponents P) (hR : HasIrreducibleAdmissibleComponents R)
    (v : FinitePlace F) (hvP : v ∉ P.exceptional) (hvR : v ∉ R.exceptional)
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    {ν : Correspondence.LocalAdditiveHaarMeasure (padicField v)}
    (hν : Correspondence.IsSelfDualMeasure (padicField v) ψ ν) (χ : HeckeCharacter F)
    {A : ℂ[X]}
    (hA : Correspondence.IsAutomorphicPairLPolynomial (padicField v) ψ ν
      (localClass (P.heckeDeterminantTwist χ)
        (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hP) v) (localClass R hR v) A) :
    A = if χ.IsUnramifiedAt v then
      (pairEulerPolynomial (P.spectralSystem.eigenvalues v hvP)
        (R.spectralSystem.eigenvalues v hvR)).comp (C (χ.finiteUniformizerValue v : ℂ) * X)
    else 1 := by
  classical
  have h := Correspondence.sphericalPairTwistLPolynomial (residuePrime v) (padicField v) ψ ν hν
    _ _ _ _ _ (hasSphericalSpectrum_padicObject P hP v hvP)
    (hasSphericalSpectrum_padicObject R hR v hvR)
    (quasicharacterBase v (χ.finiteComponent v))
    (P.isCharacterTwist_heckeDeterminantTwist_padicClass χ v (hP v).1 (hP v).2
      ((P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hP v).1)
      ((P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hP v).2)) A hA
  rwa [if_congr (conductor_quasicharacterBase_eq_zero_iff χ v) rfl rfl] at h

/-- All four actual presentations of a cuspidal pair and its dual pair are spherical at `v`. -/
def AutomorphicTwistSetup.SphericalAt
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{uF,uV} ψ r t) (v : FinitePlace F) : Prop :=
  v ∉ D.P.exceptional ∧ v ∉ D.P'.exceptional ∧ v ∉ D.Pd.exceptional ∧ v ∉ D.Pd'.exceptional

private theorem spherical_factors_twisted
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{uF,uV} ψ r t) (v : FinitePlace F) (hv : D.SphericalAt v)
    (χ : HeckeCharacter F) (z : ℂ) :
    let q := residueCardinality v
    let a := (χ.finiteUniformizerValue v : ℂ)
    (D.localFactors χ (.inr v)).lFactor z = (if χ.IsUnramifiedAt v then
      ((pairEulerPolynomial (D.P.spectralSystem.eigenvalues v hv.1)
        (D.P'.spectralSystem.eigenvalues v hv.2.1)).eval (a * spectralPoint q z))⁻¹ else 1) ∧
    (D.localFactors χ (.inr v)).dualLFactor z = (if χ.IsUnramifiedAt v then
      ((pairEulerPolynomial (D.Pd.spectralSystem.eigenvalues v hv.2.2.1)
        (D.Pd'.spectralSystem.eigenvalues v hv.2.2.2)).eval (a⁻¹ * spectralPoint q z))⁻¹ else 1) := by
  classical
  have hP := spherical_twistedPair_lPolynomial D.P D.P' D.h D.h' v hv.1 hv.2.1
    (D.additive v) (D.measure_spec v) χ (D.finiteData_specs χ v).1
  have hPd := spherical_twistedPair_lPolynomial D.Pd D.Pd' D.hd D.hd' v hv.2.2.1 hv.2.2.2
    (D.additive v) (D.measure_spec v) χ⁻¹ (D.finiteData_specs χ v).2.1
  have hInv : χ⁻¹.IsUnramifiedAt v ↔ χ.IsUnramifiedAt v :=
    ⟨fun h a ha => by
      have h' := h a ha
      change (χ.finiteComponent v a)⁻¹ = 1 at h'
      exact inv_eq_one.mp h', HeckeCharacter.isUnramifiedAt_inv⟩
  have hValue : (χ⁻¹.finiteUniformizerValue v : ℂ) = (χ.finiteUniformizerValue v : ℂ)⁻¹ :=
    Units.val_inv_eq_inv_val _
  change ((D.finiteData χ v).1.eval (spectralPoint (residueCardinality v) z))⁻¹ = _ ∧
    ((D.finiteData χ v).2.1.eval (spectralPoint (residueCardinality v) z))⁻¹ = _
  rw [hP, hPd, if_congr hInv rfl rfl, hValue]
  by_cases h : χ.IsUnramifiedAt v <;> simp [h, eval_comp]

/-- At a spherical pair, an unramified twist shifts the ordinary and dual L-factors in
opposite directions according to the uniformizer value. -/
theorem spherical_factors_of_unramified_twist
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{uF,uV} ψ r t) (v : FinitePlace F) (hv : D.SphericalAt v)
    (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt v) (c : ℂ)
    (hc : spectralPoint (residueCardinality v) c = (χ.finiteUniformizerValue v : ℂ)) (z : ℂ) :
    (D.localFactors χ (.inr v)).lFactor z = (D.localFactors 1 (.inr v)).lFactor (c + z) ∧
    (D.localFactors χ (.inr v)).dualLFactor z = (D.localFactors 1 (.inr v)).dualLFactor (-c + z) := by
  classical
  have hq := FinitePairFactorChoice.one_lt_residueCardinality v
  have h₁ : (1 : HeckeCharacter F).IsUnramifiedAt v := fun _ _ => rfl
  have hcd : spectralPoint (residueCardinality v) (-c) = (χ.finiteUniformizerValue v : ℂ)⁻¹ := by
    rw [← hc]
    simp only [spectralPoint, neg_neg, Complex.cpow_neg, inv_inv]
  have hv₁ := spherical_factors_twisted D v hv 1 (c + z)
  have hvd := spherical_factors_twisted D v hv 1 (-c + z)
  have htw := spherical_factors_twisted D v hv χ z
  have hvalue₁ : ((1 : HeckeCharacter F).finiteUniformizerValue v : ℂ) = 1 := rfl
  simp only [h₁, ite_true, hvalue₁, inv_one, one_mul, spectralPoint_add hq, hc, hcd] at hv₁ hvd
  simp only [hχ, ite_true] at htw
  exact ⟨htw.1.trans (by simpa only [mul_comm] using hv₁.1.symm),
    htw.2.trans (by simpa only [mul_comm] using hvd.2.symm)⟩

/-- At a spherical pair, a ramified twist makes both L-factors one. -/
theorem spherical_factors_of_ramified_twist
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{uF,uV} ψ r t) (v : FinitePlace F) (hv : D.SphericalAt v)
    (χ : HeckeCharacter F) (hχ : ¬χ.IsUnramifiedAt v) (z : ℂ) :
    (D.localFactors χ (.inr v)).lFactor z = 1 ∧ (D.localFactors χ (.inr v)).dualLFactor z = 1 := by
  simpa only [hχ, ite_false] using spherical_factors_twisted D v hv χ z

/-- At the trivial character the two finite L-factors are the untwisted spherical values. -/
theorem spherical_factors_one
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{uF,uV} ψ r t) (v : FinitePlace F) (hv : D.SphericalAt v)
    (z : ℂ) :
    (D.localFactors 1 (.inr v)).lFactor z =
      ((pairEulerPolynomial (D.P.spectralSystem.eigenvalues v hv.1)
        (D.P'.spectralSystem.eigenvalues v hv.2.1)).eval (spectralPoint (residueCardinality v) z))⁻¹ ∧
    (D.localFactors 1 (.inr v)).dualLFactor z =
      ((pairEulerPolynomial (D.Pd.spectralSystem.eigenvalues v hv.2.2.1)
        (D.Pd'.spectralSystem.eigenvalues v hv.2.2.2)).eval (spectralPoint (residueCardinality v) z))⁻¹ := by
  have h₁ : (1 : HeckeCharacter F).IsUnramifiedAt v := fun _ _ => rfl
  have hvalue₁ : ((1 : HeckeCharacter F).finiteUniformizerValue v : ℂ) = 1 := rfl
  simpa only [h₁, ite_true, hvalue₁, inv_one, one_mul] using spherical_factors_twisted D v hv 1 z

end LocalFactors

section NormTwist

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

/-- At a place of ramification index one, norm pullback preserves and detects
triviality on integral units of a Hecke character. -/
theorem unramified_comp_ideleClassNorm_iff (χ : HeckeCharacter F) (v : FinitePlace F)
    (w : FinitePlacesAbove E v) (he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1) :
    HeckeCharacter.IsUnramifiedAt (χ.comp (ideleClassNorm (K := F) (L := E))) w.1 ↔ χ.IsUnramifiedAt v := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, hnb⟩ := FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one
      v w.1 he a (valuation_eq_one_of_integralUnit ha)
    have hab : FiniteExtension.localUnitNorm v w.1 b = a := Units.ext hnb
    have h' := h b (HeckeCharacter.mem_units_of_valued_eq_one hb)
    rwa [Automorphic.Unramified.finiteComponent_comp_ideleClassNorm χ v w b, hab] at h'
  · intro h b hb
    rw [Automorphic.Unramified.finiteComponent_comp_ideleClassNorm χ v w b]
    exact h _ (FiniteExtension.localUnitNorm_integral v w.1 hb)

private theorem norm_uniformizerValue (χ : HeckeCharacter F) (v : FinitePlace F)
    (w : FinitePlacesAbove E v) (he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1)
    (hχ : χ.IsUnramifiedAt v) :
    HeckeCharacter.finiteUniformizerValue (χ.comp (ideleClassNorm (K := F) (L := E))) w.1 =
      χ.finiteUniformizerValue v ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
  let χE : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
  let ϖ := (padicField v).canonicalTopologicalData.uniformizerUnit
  let ϖ' := Units.map (FiniteExtension.completionMap v w.1).toMonoidHom ϖ
  have hϖ' : Valued.v (ϖ' : FiniteCompletion E w.1) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (FiniteExtension.completionMap v w.1 (ϖ : FiniteCompletion F v)) = _
    rw [FiniteExtension.valuation_completionMap, he, pow_one,
      FiniteAdelicGL.completion_uniformizer_value]
  have hnorm : FiniteExtension.localUnitNorm v w.1 ϖ' = ϖ ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
    apply Units.ext
    rw [FiniteExtension.localUnitNorm_val]
    change FiniteExtension.localNorm v w.1
      (FiniteExtension.completionMap v w.1 (ϖ : FiniteCompletion F v)) = _
    rw [FiniteExtension.localNorm_algebraMap, localDegree_eq, he, one_mul, Units.val_pow_eq_pow_val]
  have hχE := (unramified_comp_ideleClassNorm_iff χ v w he).mpr hχ
  change χE.finiteComponent w.1 (padicField w.1).canonicalTopologicalData.uniformizerUnit = _
  rw [χE.finiteComponent_eq_of_valued_eq hχE
      ((FiniteAdelicGL.completion_uniformizer_value w.1).trans hϖ'.symm),
    Automorphic.Unramified.finiteComponent_comp_ideleClassNorm χ v w ϖ', hnorm, map_pow]
  rfl

private theorem spectralPoint_above (v : FinitePlace F) (w : FinitePlacesAbove E v) (c : ℂ) :
    spectralPoint (residueCardinality w.1) c =
      spectralPoint (residueCardinality v) c ^ w.1.asIdeal.inertiaDeg (𝓞 F) := by
  unfold residueCardinality
  rw [Langlands.Global.RankinSelbergGlobal.EqualEulerPointwise.residueCardinality_canonical w.1,
    ← Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1.asIdeal,
    ← Langlands.Global.RankinSelbergGlobal.EqualEulerPointwise.residueCardinality_canonical v]
  simp only [spectralPoint, Nat.cast_pow, ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
variable {I : Type uI} [Fintype I]
variable {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψE : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles E)} {r t m n : ℕ}

/-- At a spherical place with ramification index one in the extension, matching
ordinary and dual pair L-factors remain matched after determinant twisting the
first member downstairs and by the norm character upstairs. -/
def WeakInductionGoodPairTwistStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (I : Type uI) [Fintype I]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    {ψE : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles E)} {r t m n : ℕ}
    (D : AutomorphicTwistSetup.{uF,uV} ψ r t) (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n)
    (v : FinitePlace F), D.SphericalAt v →
    (∀ (i : I) (w : FinitePlacesAbove E v), (U i).SphericalAt w.1) →
    (∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 F) = 1) →
    (∀ z : ℂ,
      (D.localFactors 1 (.inr v)).lFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors 1) (.inr v)).lFactor z ∧
      (D.localFactors 1 (.inr v)).dualLFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors 1) (.inr v)).dualLFactor z) →
    ∀ (χ : HeckeCharacter F) (z : ℂ),
      let χE : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
      (D.localFactors χ (.inr v)).lFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors χE) (.inr v)).lFactor z ∧
      (D.localFactors χ (.inr v)).dualLFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors χE) (.inr v)).dualLFactor z

set_option maxHeartbeats 1000000 in
theorem weakInductionGoodPairTwist : WeakInductionGoodPairTwistStatement.{uF,uE,uV,uW,uI} := by
  classical
  intro F E _ _ _ _ _ _ _ I _ ψ ψE r t m n D U v hD hU he hBase χ z
  let χE : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
  let factors (ξ : HeckeCharacter E) (i : I) := (U i).localFactors ξ
  change _ = (numberFieldProductFactors (factors χE) (.inr v)).lFactor z ∧
    _ = (numberFieldProductFactors (factors χE) (.inr v)).dualLFactor z
  rw [(numberFieldProductFactors_finite (factors χE) v z).1,
    (numberFieldProductFactors_finite (factors χE) v z).2.1]
  by_cases hχ : χ.IsUnramifiedAt v
  · obtain ⟨c, hc, -⟩ := HighlyRamified.exists_spectralPoint_eq
      (FinitePairFactorChoice.one_lt_residueCardinality v) (χ.finiteUniformizerValue v).ne_zero
    have hc' (w : FinitePlacesAbove E v) :
        spectralPoint (residueCardinality w.1) c = (χE.finiteUniformizerValue w.1 : ℂ) := by
      rw [spectralPoint_above, hc, norm_uniformizerValue χ v w (he w) hχ,
        Units.val_pow_eq_pow_val]
    have hU' (w : FinitePlacesAbove E v) (i : I) := spherical_factors_of_unramified_twist (U i)
      w.1 (hU i w) χE ((unramified_comp_ideleClassNorm_iff χ v w (he w)).mpr hχ) c (hc' w) z
    have hd := spherical_factors_of_unramified_twist D v hD χ hχ c hc z
    have hb := (hBase (c + z)).1
    have hbd := (hBase (-c + z)).2
    rw [(numberFieldProductFactors_finite (factors 1) v (c + z)).1] at hb
    rw [(numberFieldProductFactors_finite (factors 1) v (-c + z)).2.1] at hbd
    simp only [factors]
    simp_rw [fun w i => (hU' w i).1, fun w i => (hU' w i).2]
    exact ⟨hd.1.trans hb, hd.2.trans hbd⟩
  · have hU' (w : FinitePlacesAbove E v) (i : I) := spherical_factors_of_ramified_twist (U i)
      w.1 (hU i w) χE (fun h => hχ ((unramified_comp_ideleClassNorm_iff χ v w (he w)).mp h)) z
    have hd := spherical_factors_of_ramified_twist D v hD χ hχ z
    simp only [factors]
    simp_rw [fun w i => (hU' w i).1, fun w i => (hU' w i).2, Finset.prod_const_one]
    exact hd

end NormTwist

end Langlands.Global.CuspidalPairFunctionalEquation
