import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction
import Langlands.BaseChange.TraceAdditiveConductor
import Langlands.Representation.Conductor.FieldEquivTransport

/-!
# Conductor reduction with the trace character and orbit transport

The local input uses the actual trace pullback and gives an independent
newvector certificate for each orbit block. Conductor invariance and the
additive shift follow from the local-field data.
-/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)

universe u v uV uW

/-- The remaining local epsilon data with the trace character constructed and
the finite conductor certified separately for each orbit block. -/
def CuspidalSigmaLiftTraceEpsilonDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), (hcyc : IsCyclicAlgebra σ l) →
    ∀ (k : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (k + 1) F) V)
      (hπ : IsAdmissible π), GeneralLinear.IsSupercuspidal π → π.IsIrreducible →
    ∀ (s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
      (W₁ : Type uW) [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
      GeneralLinear.IsSupercuspidal P₁ → P₁.IsIrreducible →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E) W)
      (hP : IsAdmissible P),
      Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
        (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (A : SigmaIntertwiner σ (k + 1) P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_t2Space E (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (k + 1)
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ f d : ℕ, IsResidueDegree F E f → IsDifferentExponent F E d →
    ∀ X : Finset (Fˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
      letI : Module.Finite F E := hcyc.1
      ∃ (ψF : UnitaryAdditiveCharacter F)
        (νF : letI := borel F; AdditiveHaarMeasure F)
        (νE : letI := borel E; AdditiveHaarMeasure E)
        (aF : (Fˣ →* ℂˣ) → ℕ) (aOrbit : Fin s → ℕ)
        (eF : (Fˣ →* ℂˣ) → ℂˣ × ℤ) (eOrbit : Fin s → ℂˣ × ℤ) (eP : ℂˣ × ℤ),
        let ψE : UnitaryAdditiveCharacter E := ψF.tracePullback
        (LocalFieldData.ofInstances F).additiveConductor ψF = 0 ∧
        (∀ κ ∈ X, IsStandardEpsilonConductor ψF νF
          (twist (κ.comp GeneralLinear.determinant) π) (aF κ) (eF κ)) ∧
        (∀ i : Fin s, IsStandardEpsilonConductor ψE νE
          (P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom) (aOrbit i) (eOrbit i)) ∧
        OrbitProductEpsilonMultiplicativity ψE νE P eOrbit eP ∧
        EpsilonMonomialProductComparison (LocalFieldData.ofInstances F).residueCardinality
          (LocalFieldData.ofInstances E).residueCardinality X eF eP

/-- The trace-character epsilon data suffice for the exact four-universe
cuspidal sigma-lift conductor identity. -/
def CuspidalSigmaLiftConductorFromTraceEpsilonStatement : Prop :=
  CuspidalSigmaLiftTraceEpsilonDataStatement.{u, v, uV, uW} →
    CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorFromTraceEpsilon :
    CuspidalSigmaLiftConductorFromTraceEpsilonStatement.{u, v, uV, uW} := by
  intro hdata
  apply cuspidalSigmaLiftConductorFromLocalEpsilon
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc k V _ _ π hπ hsuper hπirr
    s k₁ hrank W₁ _ _ P₁ hP₁super hP₁irr W _ _ P hP horbit A c hlift f d hf hd X hX
  obtain ⟨ψF, νF, νE, aF, aOrbit, eF, eOrbit, eP, hψF, hF, hOrbit, hprod, hcomp⟩ :=
    hdata F E σ l hcyc k V π hπ hsuper hπirr s k₁ hrank W₁ P₁ hP₁super hP₁irr
      W P hP horbit A c hlift f d hf hd X hX
  let : Module.Finite F E := hcyc.1
  let ψE : UnitaryAdditiveCharacter E := ψF.tracePullback
  have htrace : ∀ x : E, ψE x = ψF (Algebra.trace F E x) := fun _ => rfl
  have hψE := hd.additiveConductor_of_trace ψF ψE hψF htrace
  have hnew (i : Fin s) : Conductor.IsNewvectorConductor P₁ (aOrbit i) := by
    let e := σ ^ (i : ℕ)
    exact (Conductor.isNewvectorConductor_comp_fieldEquiv_iff e.toRingEquiv
      (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
      (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap) P₁ (aOrbit i)).mp
      (hOrbit i).2.1
  have hs : 0 < s := by
    by_contra! h
    have hs0 : s = 0 := by omega
    simp [hs0] at hrank
  let i₀ : Fin s := ⟨0, hs⟩
  refine ⟨ψF, ψE, νF, νE, aF, aOrbit i₀, eF, eOrbit, eP,
    ⟨htrace, hψF, hψE⟩, hF, hnew i₀, ?_, hprod, hcomp⟩
  intro i
  have ha : aOrbit i = aOrbit i₀ := (hnew i).unique (hnew i₀)
  exact ha ▸ hOrbit i

end Langlands.BaseChange
