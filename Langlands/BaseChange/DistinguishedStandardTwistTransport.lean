import Langlands.BaseChange.DeterminantTwistFieldEquiv
import Langlands.BaseChange.DistinguishedStandardEpsilonExponent
import Langlands.BaseChange.EpsilonComparisonReindex
import Langlands.BaseChange.StandardTwistDistinguishedEpsilon

/-! # Transport of the distinguished standard epsilon comparison -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ uI uF uE uV uW

namespace Langlands.BaseChange

open Automorphic Global Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open GeneralLinear RankinSelberg
open scoped PadicField.CanonicalLocalField

section Transport

local instance transportRationalGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance transportContinuousGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance transportSmoothGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance transportFormsGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance transportLocalGroup {K : Type u} [Field K] [NumberField K]
    {n : ℕ} {v : FinitePlace K} (D : LocalRealization K n v) :
    AddCommGroup D.Space := Submodule.addCommGroup _

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  (v : FinitePlace K) (w : FinitePlace L) {r : ℕ}
  {T Td : CuspidalOperatorRealization K r} {U Ud : CuspidalOperatorRealization L r}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (Dd : CuspidalSpectralPresentation.{u, uQ} Td)
  (Q : CuspidalSpectralPresentation.{u, uQ} U) (Qd : CuspidalSpectralPresentation.{u, uQ} Ud)
  (hD : HasIrreducibleAdmissibleComponents D) (hDd : HasIrreducibleAdmissibleComponents Dd)
  (hQ : HasIrreducibleAdmissibleComponents Q) (hQd : HasIrreducibleAdmissibleComponents Qd)
  {I : Type uI} [Fintype I] (χ : I → HeckeCharacter K)

variable
  (cF : ∀ i, FinitePairFactorChoice (standardGlobalAdditiveCharacter K)
    (D.heckeDeterminantTwist (χ i)) (ConstantFunctions.rankOneSpectralPresentation.{u, uQ} K)
    (Dd.heckeDeterminantTwist (χ i)⁻¹) (ConstantFunctions.rankOneSpectralPresentation.{u, uQ} K)
    (D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i) hD)
    (ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K)
    (Dd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i)⁻¹ hDd)
    (ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K))
  (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L)
    Q (ConstantFunctions.rankOneSpectralPresentation.{u, uQ} L)
    Qd (ConstantFunctions.rankOneSpectralPresentation.{u, uQ} L)
    hQ (ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} L)
    hQd (ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} L))
  {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [TopologicalSpace E] [ValuativeRel E] [IsNonarchimedeanLocalField E]
  (a : F ≃+* (padicField v).Carrier) (b : E ≃+* (padicField w).Carrier)
  (ha : @Continuous F (padicField v).Carrier ‹TopologicalSpace F›
    (padicField v).canonicalTopologicalData.topology a)
  (ha' : @Continuous (padicField v).Carrier F (padicField v).canonicalTopologicalData.topology
    ‹TopologicalSpace F› a.symm)
  (hb : @Continuous E (padicField w).Carrier ‹TopologicalSpace E›
    (padicField w).canonicalTopologicalData.topology b)
  (hb' : @Continuous (padicField w).Carrier E (padicField w).canonicalTopologicalData.topology
    ‹TopologicalSpace E› b.symm)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (P : Representation ℂ (GeneralLinear (r + 1) E) W)
  (R : Representation ℂ (GeneralLinear (r + 1) (padicField v).Carrier) V)
  (S : Representation ℂ (GeneralLinear (r + 1) (padicField w).Carrier) W)
  (μ : (padicField v).Carrierˣ →* ℂˣ) (η : (padicField w).Carrierˣ →* ℂˣ)
  (X : Finset (Fˣ →* ℂˣ)) (index : I ≃ ↥X)

set_option maxHeartbeats 2400000 in
/-- A comparison at two finite completions gives the comparison of the original local
standard factors, with the Hecke twists reindexed by their local characters. -/
theorem distinguishedStandardTwistTransport
    (hμ : (padicField v).canonicalTopologicalData.IsUnramifiedCharacter μ)
    (hη : (padicField w).canonicalTopologicalData.IsUnramifiedCharacter η)
    (hπ : π.Equiv (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom)))
    (hP : P.Equiv (S.comp (Matrix.GeneralLinearGroup.map b.toRingHom)))
    (hR : (twist (μ.comp determinant) R).Equiv (D.localComponent v).representation)
    (hS : (twist (η.comp determinant) S).Equiv (Q.localComponent w).representation)
    (hindex : ∀ i, (index i : Fˣ →* ℂˣ) =
      ((χ i).finiteComponent v).toMonoidHom.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom)
    (hcomp : EpsilonMonomialProductComparison (residueCardinality v) (residueCardinality w)
      Finset.univ (fun i => (cF i).epsilon v) (cE.epsilon w))
    (eF : (Fˣ →* ℂˣ) → ℂˣ × ℤ) (eE : ℂˣ × ℤ)
    (heF : ∀ κ ∈ X, IsEpsilonFactorAgainstTrivialCharacter
      (standardCompletionAdditivePullback v a ha) (standardCompletionSelfDualPullback v a ha ha').val
      (twist (κ.comp determinant) π) (eF κ))
    (heE : IsEpsilonFactorAgainstTrivialCharacter
      (standardCompletionAdditivePullback w b hb) (standardCompletionSelfDualPullback w b hb hb').val P eE) :
    EpsilonMonomialProductComparison (LocalFieldData.ofInstances F).residueCardinality
      (LocalFieldData.ofInstances E).residueCardinality X eF eE := by
  have hF (i : I) : ((cF i).epsilon v).2 = (eF (index i)).2 := by
    let κ := ((χ i).finiteComponent v).toMonoidHom
    let κdet := κ.comp (determinant (n := r + 1))
    let μdet := μ.comp (determinant (n := r + 1))
    have hπ' : (twist ((index i : Fˣ →* ℂˣ).comp determinant) π).Equiv
        ((twist κdet R).comp (Matrix.GeneralLinearGroup.map a.toRingHom)) := by
      rw [hindex i]
      exact pullbackDeterminantTwistEquiv a hπ κ
    have hcomm : twist μdet (twist κdet R) = twist κdet (twist μdet R) := by
      rw [twist_twist, twist_twist, mul_comm μdet κdet]
    have hκdet : (HeckeCharacter.finiteLocalDeterminant (r + 1) (χ i) v).toMonoidHom = κdet := by
      apply MonoidHom.ext
      intro g
      exact HeckeCharacter.finiteLocalDeterminant_eq_finiteComponent_det (χ i) (r + 1) v g
    have htwist : (twist κdet (D.localComponent v).representation).Equiv
        ((D.heckeDeterminantTwist (χ i)).localComponent v).representation := by
      rw [← hκdet]
      exact ((D.localComponent v).heckeDeterminantTwistRepresentationEquiv (χ i)).trans
        (D.heckeDeterminantTwistLocalComponentEquiv (χ i) v).symm
    have hR' : (twist μdet (twist κdet R)).Equiv
        ((D.heckeDeterminantTwist (χ i)).localComponent v).representation := by
      rw [hcomm]
      exact (twistEquiv κdet hR).trans htwist
    exact distinguishedStandardEpsilonExponent v (cF i) a ha ha' _ (twist κdet R) μ
      hμ ⟨hπ'⟩ ⟨hR'⟩ _ (heF (index i) (index i).property)
  have hE : (cE.epsilon w).2 = eE.2 :=
    distinguishedStandardEpsilonExponent w cE b hb hb' P S η hη ⟨hP⟩ ⟨hS⟩ eE heE
  have hqF : residueCardinality v = (LocalFieldData.ofInstances F).residueCardinality :=
    (LocalFieldData.ofInstances F).residueCardinality_of_continuous_ringEquiv
      (padicField v).canonicalLocalFieldData a ha ha'
  have hqE : residueCardinality w = (LocalFieldData.ofInstances E).residueCardinality :=
    (LocalFieldData.ofInstances E).residueCardinality_of_continuous_ringEquiv
      (padicField w).canonicalLocalFieldData b hb hb'
  rw [← hqF, ← hqE]
  exact epsilonComparisonReindex I _ X index _ _ _ _ eF eE hF hE hcomp

end Transport

end Langlands.BaseChange
