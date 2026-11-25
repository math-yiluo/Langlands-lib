import Langlands.BaseChange.CompletionRelativeFieldInvariants
import Langlands.BaseChange.PadicUnramifiedNormFactors
import Langlands.BaseChange.SphericalStandardFactorsAtCompletion
import Langlands.BaseChange.UnramifiedStandardEpsilonExponent
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Global.Factors.DistinguishedFiniteStandardEpsilon
import Langlands.Representation.Induction.BinaryProduct

/-! # Pulling back the distinguished standard epsilon exponent -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ uF uE uV uW

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.AdelicFunctoriality Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open GeneralLinear RankinSelberg HarmonicAnalysis MeasureTheory
open scoped NumberField FiniteExtension PadicField.CanonicalLocalField

section StandardAdditive

variable {K : Type u} [Field K] [NumberField K] (v : FinitePlace K)
  {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (a : F ≃+* (padicField v).Carrier)
  (ha : @Continuous F (padicField v).Carrier ‹TopologicalSpace F›
    (padicField v).canonicalTopologicalData.topology a)
  (ha' : @Continuous (padicField v).Carrier F
    (padicField v).canonicalTopologicalData.topology ‹TopologicalSpace F› a.symm)

/-- The pullback of the standard finite adelic character at the chosen completion. -/
abbrev standardCompletionAdditivePullback : UnitaryAdditiveCharacter F :=
  completionAdditivePullback (padicField v) a ha (standardFiniteAdditiveComponent K v)

/-- The pullback of the unique self-dual measure at the standard finite character. -/
def standardCompletionSelfDualPullback :
    AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances F)
      (standardCompletionAdditivePullback v a ha) := by
  let μ := localSelfDualHaar (padicField v) (standardFiniteAdditiveComponent K v)
  let ν : letI := borel F; AdditiveHaarMeasure F :=
    completionHaarPullback (padicField v) a ha ha' μ
  exact ⟨ν, completionHaarPullback_isSelfDual (padicField v) a ha ha'
    (standardFiniteAdditiveComponent K v) μ (isSelfDual_localSelfDualHaar _ _)⟩

end StandardAdditive

/-- The normalized order in a completion package is unaffected by the prime
equality used to package it over the lower residue prime. -/
private theorem completion_order_atPrime {L : Type u} [Field L] [NumberField L]
    (w : FinitePlace L) {p : ℕ} [Fact p.Prime] (h : residuePrime w = p)
    (x : w.adicCompletion L) :
    (padicFieldAt w h).canonicalTopologicalData.ord x =
      (padicField w).canonicalTopologicalData.ord x := by
  subst p
  rfl

/-- Pullback by the actual completed determinant norm preserves unramified
characters. The upper order is multiplied by the inertia degree under the norm. -/
theorem completion_unramified_comp_norm
    {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : FinitePlace K) (w : FinitePlacesAbove L v)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ : (padicField v).canonicalTopologicalData.IsUnramifiedCharacter χ) :
    (padicField w.1).canonicalTopologicalData.IsUnramifiedCharacter
      (χ.comp (LocalClassField.normUnits (v.adicCompletion K) (w.1.adicCompletion L))) := by
  let F := padicField v
  let E := towerPadicField v w.1
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  let := towerPadicField_isScalarTower v w.1
  change T.IsUnramifiedCharacter χ at hχ
  rw [PadicField.TopologicalData.IsUnramifiedCharacter, ← T.ker_ordUnits] at hχ
  rw [PadicField.TopologicalData.IsUnramifiedCharacter,
    ← (padicField w.1).canonicalTopologicalData.ker_ordUnits]
  intro x hx
  let y := LocalClassField.normUnits (v.adicCompletion K) (w.1.adicCompletion L) x
  change y ∈ χ.ker
  apply hχ
  change T.ord (y : v.adicCompletion K) = 0
  change (padicField w.1).canonicalTopologicalData.ord (x : w.1.adicCompletion L) = 0 at hx
  have ho := ord_localNorm_eq_residueDegree_mul T S (completion_isResidueDegree v w.1) x
  change T.ord (y : v.adicCompletion K) = _ at ho
  rw [ho, show S.ord (x : w.1.adicCompletion L) = _ from
    completion_order_atPrime w.1 (residuePrime_eq v w.1) x, hx, mul_zero]

/-- The pulled-back standard characters have the trace relation whenever the
two completion isomorphisms preserve the relative scalar embedding. -/
theorem standardCompletionAdditivePullback_trace
    {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : FinitePlace K) (w : FinitePlacesAbove L v)
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {E : Type uE} [Field E] [TopologicalSpace E] [ValuativeRel E] [IsNonarchimedeanLocalField E] [Algebra F E]
    (a : F ≃+* (padicField v).Carrier) (b : E ≃+* (padicField w.1).Carrier)
    (ha : @Continuous F (padicField v).Carrier ‹TopologicalSpace F›
      (padicField v).canonicalTopologicalData.topology a)
    (hb : @Continuous E (padicField w.1).Carrier ‹TopologicalSpace E›
      (padicField w.1).canonicalTopologicalData.topology b)
    (hab : (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).comp a.toRingHom =
      b.toRingHom.comp (algebraMap F E)) (x : E) :
    standardCompletionAdditivePullback w.1 b hb x =
      standardCompletionAdditivePullback v a ha (Algebra.trace F E x) := by
  change standardFiniteAdditiveComponent L w.1 (b x) =
    standardFiniteAdditiveComponent K v (a (Algebra.trace F E x))
  rw [standardFiniteAdditiveComponent_trace v w.1,
    Algebra.trace_eq_of_equiv_equiv a b hab, a.apply_symm_apply]

section Exponent

private theorem compGeneralLinearMap_refl {F : Type*} [Field F] {m : ℕ}
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (π : Representation ℂ (GeneralLinear m F) Z) :
    π.comp (Matrix.GeneralLinearGroup.map (RingEquiv.refl F).toRingHom) = π := by
  rw [show (RingEquiv.refl F).toRingHom = RingHom.id F from rfl,
    Matrix.GeneralLinearGroup.map_id, MonoidHom.comp_id]

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  (v : FinitePlace K) {r : ℕ} {T Td : CuspidalOperatorRealization K r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
  {hP : HasIrreducibleAdmissibleComponents P} {hPd : HasIrreducibleAdmissibleComponents Pd}

local instance distinguishedExponentRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance distinguishedExponentContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance distinguishedExponentSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance distinguishedExponentFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance distinguishedExponentLocalGroup {n : ℕ} (S : LocalRealization K n v) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable (c : FinitePairFactorChoice (standardGlobalAdditiveCharacter K)
    P (ConstantFunctions.rankOneSpectralPresentation.{u, uQ} K)
    Pd (ConstantFunctions.rankOneSpectralPresentation.{u, uQ} K)
    hP (ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K)
    hPd (ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K))
  {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  (a : F ≃+* (padicField v).Carrier)
  (ha : @Continuous F (padicField v).Carrier ‹TopologicalSpace F›
    (padicField v).canonicalTopologicalData.topology a)
  (ha' : @Continuous (padicField v).Carrier F (padicField v).canonicalTopologicalData.topology
    ‹TopologicalSpace F› a.symm)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (R : Representation ℂ (GeneralLinear (r + 1) (padicField v).Carrier) W)
  (χ : (padicField v).Carrierˣ →* ℂˣ)

/-- If the actual finite component realizes an unramified determinant twist
of a supplied local representation, its standard epsilon exponent is that
of the given local certificate at the pulled-back standard data. -/
def DistinguishedStandardEpsilonExponentStatement : Prop :=
  (padicField v).canonicalTopologicalData.IsUnramifiedCharacter χ →
  Nonempty (Representation.Equiv ρ (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) →
  Nonempty (Representation.Equiv (twist (χ.comp determinant) R)
    (P.localComponent v).representation) →
  ∀ e : ℂˣ × ℤ, IsEpsilonFactorAgainstTrivialCharacter
    (standardCompletionAdditivePullback v a ha)
    (standardCompletionSelfDualPullback v a ha ha').val ρ e →
    (c.epsilon v).2 = e.2

set_option maxHeartbeats 2500000 in
theorem distinguishedStandardEpsilonExponent :
    DistinguishedStandardEpsilonExponentStatement v c a ha ha' ρ R χ := by
  intro hχ ⟨α⟩ ⟨β⟩ e he
  let D₀ := padicField v
  let : TopologicalSpace D₀.Carrier := D₀.canonicalTopologicalData.topology
  let : ValuativeRel D₀.Carrier := D₀.canonicalTopologicalData.valuativeRel
  let : IsNonarchimedeanLocalField D₀.Carrier := D₀.canonicalTopologicalData.localField
  let := borel D₀.Carrier
  let : BorelSpace D₀.Carrier := ⟨rfl⟩
  let ψ := standardFiniteAdditiveComponent K v
  let μ := localSelfDualHaar D₀ ψ
  have hμ : IsSelfDualMeasure D₀ ψ μ := isSelfDual_localSelfDualHaar D₀ ψ
  have hmap :
      letI := borel F
      letI := borel D₀.Carrier
      μ.measure = (completionHaarPullback D₀ a ha ha' μ).measure.map a := by
    let := borel F
    let : BorelSpace F := ⟨rfl⟩
    exact (congrArg AdditiveHaarMeasure.measure
      (HarmonicAnalysis.FieldTransport.haarMeasure_symm a.symm ha' ha μ)).symm
  have hR : IsEpsilonFactorAgainstTrivialCharacter ψ μ R e := by
    apply (RankinSelberg.FieldTransport.isLocalPairEpsilonFactor_comp_iff a ha ha'
      (ψ := standardCompletionAdditivePullback v a ha) (ψ' := ψ)
      (fun x => rfl) hmap R (rankOneCharacter (1 : D₀.Carrierˣ →* ℂˣ)) e).mpr
    let := borel F
    let : BorelSpace F := ⟨rfl⟩
    let := borel (GeneralLinear 1 F)
    let : BorelSpace (GeneralLinear 1 F) := ⟨rfl⟩
    let := borel (upperUnipotent 1 F)
    let : BorelSpace (upperUnipotent 1 F) := ⟨rfl⟩
    let := borel (LeftUnipotentQuotient 0 F)
    have htriv : (rankOneCharacter (1 : D₀.Carrierˣ →* ℂˣ)).comp
        (Matrix.GeneralLinearGroup.map a.toRingHom) = rankOneCharacter (1 : Fˣ →* ℂˣ) := rfl
    exact (IsPairEpsilonFactor.congr_equiv α (equivOfRepresentationEq htriv.symm)).mp he
  obtain ⟨e', h₂, he'⟩ :=
    unramifiedStandardEpsilonExponent (residuePrime v) D₀ ψ ⟨μ, hμ⟩ R χ hχ e hR
  have hψc : c.additive v = ψ := by
    apply UnitaryAdditiveCharacter.ext
    intro x
    change c.additive v x = standardFiniteAdditiveComponent K v x
    rw [c.additive_spec v, ← isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K v]
  have hμc : c.measure v = μ := by
    apply eq_localSelfDualHaar D₀ ψ
    rw [← hψc]
    exact c.measure_spec v
  let b := RingEquiv.refl D₀.Carrier
  have hb : Continuous b := continuous_id
  have hb' : Continuous b.symm := continuous_id
  obtain ⟨βC⟩ := ConstantFunctions.rankOneSpectralPresentation_localTrivialEquiv.{u, uQ} K v
  let β' := (equivOfRepresentationEq (compGeneralLinearMap_refl (twist (χ.comp determinant) R)).symm).trans
    (BinaryTensor.compEquiv β (Matrix.GeneralLinearGroup.map b.toRingHom))
  let βC' := (BinaryTensor.compEquiv βC.symm (Matrix.GeneralLinearGroup.map b.toRingHom)).trans
    (equivOfRepresentationEq (compGeneralLinearMap_refl (rankOneCharacter (1 : D₀.Carrierˣ →* ℂˣ))))
  have he'' : IsEpsilonFactorAgainstTrivialCharacter (completionAdditivePullback D₀ b hb (c.additive v))
      (completionHaarPullback D₀ b hb hb' (c.measure v)) (twist (χ.comp determinant) R) e' := by
    rw [hψc, hμc]
    have hp : completionAdditivePullback D₀ b hb ψ = ψ := by ext x; rfl
    have hm : completionHaarPullback D₀ b hb hb' μ = μ := by
      apply AdditiveHaarMeasure.ext
      change μ.measure.map id = μ.measure
      exact Measure.map_id
    rw [hp, hm]
    exact he'
  exact (congrArg Prod.snd (distinguishedFiniteStandardEpsilon c v b hb hb'
    (twist (χ.comp determinant) R) β' βC' e' he'' |>.1)).trans h₂

end Exponent

end Langlands.BaseChange
