import Langlands.BaseChange.DistinguishedTensorLiftTransport
import Langlands.BaseChange.HeckeTwistCompletionEquivalences
import Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalProof
import Langlands.Global.Factors.CuspidalNormPowerTwist
import Langlands.Global.Factors.HeckeFiniteEpsilon
import Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftAnyDegreeStatement

/-! # Applying cyclic lift to a prescribed lower presentation -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Automorphic Correspondence GeneralLinear Global Global.AdelicFunctoriality Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open HarmonicAnalysis TraceFormula
open scoped NumberField FiniteExtension NNReal

universe uV

local instance lowerCyclicRationalGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance lowerCyclicContinuousGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance lowerCyclicSmoothGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance lowerCyclicFormsGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance lowerCyclicLocalGroup {K : Type} [Field K] [NumberField K]
    {n : ℕ} {p : FinitePlace K} (D : LocalRealization K n p) :
    AddCommGroup D.Space := Submodule.addCommGroup _

section Normalize

variable {K : Type} [Field K] [NumberField K]

private theorem finiteComponent_isUnramifiedCharacter (ν : HeckeCharacter K) (p : FinitePlace K)
    (hν : ν.IsUnramifiedAt p) :
    (padicField p).canonicalTopologicalData.IsUnramifiedCharacter (ν.finiteComponent p).toMonoidHom := by
  intro x hx
  let T := (padicField p).canonicalTopologicalData
  have ha : T.normalizedAbs (x : (padicField p).Carrier) = 1 := by
    have he : T.normalizedAbsUnits x = 1 := MonoidHom.mem_ker.mp hx
    change (((T.normalizedAbsUnits x).val : ℝ≥0) : ℝ) = 1
    rw [he]
    rfl
  have hd : (topologicalData p).discreteValuation (x : p.adicCompletion K) = 1 := by
    rw [topologicalData_eq_canonicalTopologicalData]
    exact (T.normalizedAbs_eq_one_iff_discreteValuation _).mp ha
  change ν.finiteComponent p x = 1
  exact ((topologicalData p).multiplicativeConductor_eq_zero_iff (ν.finiteComponent p)).mp
    (multiplicativeConductor_eq_zero_of_isUnramifiedAt ν p hν) x hd

variable [CompactSpace (AdeleQuotient K)] {r : ℕ} {T : CuspidalOperatorRealization K r}

private theorem unramifiedTwist_preservesCompletionMatching
    (D : CuspidalSpectralPresentation.{0, 0} T) (ν : HeckeCharacter K) (p : FinitePlace K)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (R : Representation ℂ (GeneralLinear (r + 1) (p.adicCompletion K)) V)
    (μ : Quasicharacter (p.adicCompletion K))
    (hμ : (padicField p).canonicalTopologicalData.IsUnramifiedCharacter μ.toMonoidHom)
    (eR : Nonempty ((twist (μ.toMonoidHom.comp determinant) R).Equiv (D.localComponent p).representation))
    (hν : ν.IsUnramifiedAt p) :
    ∃ μ' : Quasicharacter (p.adicCompletion K),
      (padicField p).canonicalTopologicalData.IsUnramifiedCharacter μ'.toMonoidHom ∧
      Nonempty ((twist (μ'.toMonoidHom.comp determinant) R).Equiv
        ((D.heckeDeterminantTwist ν).localComponent p).representation) := by
  let ξ := ν.finiteComponent p
  let μ' : Quasicharacter (p.adicCompletion K) := ξ * μ
  have hξ := finiteComponent_isUnramifiedCharacter ν p hν
  refine ⟨μ', fun x hx => ?_, ?_⟩
  · change ξ x * μ x = 1
    rw [show ξ x = 1 from hξ hx, show μ x = 1 from hμ hx, one_mul]
  · let δ := determinantQuasiCharacter (padicField p) r.succPNat (quasicharacterBase p ξ)
    have he : μ'.toMonoidHom.comp determinant = δ * μ.toMonoidHom.comp determinant :=
      MonoidHom.ext fun _ => rfl
    rw [he, ← twist_twist]
    exact eR.map fun e => (twistEquiv δ e).trans (heckeTwistAtCompletionEquiv D p ν)

end Normalize

section Lift

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  {r : ℕ} {T : CuspidalOperatorRealization K r}

set_option maxHeartbeats 7600000 in
/-- Apply the arbitrary-degree cyclic lift proposition to a lower
presentation made unitary by an everywhere unramified norm twist. -/
theorem weakCyclicLiftFromLowerPresentation
    (hLift : CuspidalCyclicBaseChangeLiftAnyDegreeStatement.{0, 0, 0})
    (σ : L ≃ₐ[K] L) (l : ℕ) (hcyc : IsCyclicAlgebra σ l)
    (hinfinite : ∀ z : NumberField.InfinitePlace K, IsCyclicShiftSplit K L z.Completion σ l)
    (p v₁ v₂ : FinitePlace K) (h₁₂ : v₁ ≠ v₂)
    (h₁ : IsCyclicShiftSplit K L (v₁.adicCompletion K) σ l)
    (h₂ : IsCyclicShiftSplit K L (v₂.adicCompletion K) σ l)
    (w : FinitePlacesAbove L p) (hw : ∀ z : FinitePlacesAbove L p, z = w)
    (D : CuspidalSpectralPresentation.{0, 0} T) (hD : HasIrreducibleAdmissibleComponents D)
    (hDs : (D.localComponent p).IsSupercuspidal)
    (hD₁ : (D.localComponent v₁).IsSupercuspidal) (hD₂ : (D.localComponent v₂).IsSupercuspidal)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (R : Representation ℂ (GeneralLinear (r + 1) (p.adicCompletion K)) V)
    (μ : Quasicharacter (p.adicCompletion K))
    (hμ : (padicField p).canonicalTopologicalData.IsUnramifiedCharacter μ.toMonoidHom)
    (eR : Nonempty ((twist (μ.toMonoidHom.comp determinant) R).Equiv (D.localComponent p).representation)) :
    ∃ (T' : CuspidalOperatorRealization K r) (U : CuspidalOperatorRealization L r)
      (D' : CuspidalSpectralPresentation.{0, 0} T') (Q : CuspidalSpectralPresentation.{0, 0} U),
      HasIrreducibleAdmissibleComponents D' ∧ HasIrreducibleAdmissibleComponents Q ∧
      ∃ μ' : Quasicharacter (p.adicCompletion K),
        (padicField p).canonicalTopologicalData.IsUnramifiedCharacter μ'.toMonoidHom ∧
        Nonempty ((twist (μ'.toMonoidHom.comp determinant) R).Equiv (D'.localComponent p).representation) ∧
        IsLiftAtDistinguishedTensor w hw σ l (D'.localComponent p) (Q.localComponent w.1) ∧
        (D'.localComponent p).IsSupercuspidal ∧ Q.spectralSystem.IsArithmeticWeakBaseChangeOf D'.spectralSystem := by
  obtain ⟨s, hu, -⟩ := NormPowerTwist.exists_normPower_twist T
  let ν := HeckeCharacter.normPower K (-s)
  let T' := T.heckeDeterminantTwist ν
  let D' := D.heckeDeterminantTwist ν
  let hD' := D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents ν hD
  obtain ⟨μ', hμ', eR'⟩ := unramifiedTwist_preservesCompletionMatching D ν p R μ hμ eR
    (HeckeCharacter.normPower_isUnramifiedAt K (-s) p)
  have hD'₁ := heckeDeterminantTwistSupercuspidal K T D ν v₁ hD₁
  have hD'₂ := heckeDeterminantTwistSupercuspidal K T D ν v₂ hD₂
  obtain ⟨U, Q, -, hweak, -, -, hloc, hQ⟩ :=
    hLift K L σ l hcyc hinfinite r T' D' hu hD' v₁ v₂ h₁₂ h₁ h₂ hD'₁ hD'₂
  have htensor : IsLiftAtDistinguishedTensor w hw σ l (D'.localComponent p) (Q.localComponent w.1) := by
    have h := hloc p w hw
    dsimp only [IsLiftAtDistinguishedTensor, tensorUniqueCompletion_toRingHom_eq]
    dsimp only [tensorPlaceAboveRepresentation, tensorPlaceAboveHom] at h
    exact h
  exact ⟨T', U, D', Q, hD', hQ, μ', hμ', eR', htensor,
    heckeDeterminantTwistSupercuspidal K T D ν p hDs, hweak⟩

end Lift

end Langlands.BaseChange
