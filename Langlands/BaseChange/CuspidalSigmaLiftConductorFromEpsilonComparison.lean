import Langlands.BaseChange.CuspidalSigmaLiftTraceEpsilonFactors
import Langlands.BaseChange.CharZeroTraceConductorPremises
import Langlands.Representation.Conductor.FieldEquivTransport

/-!
# The conductor formula from the cross-field epsilon comparison

All same-field local certificates are constructed; only the comparison of the
epsilon monomials of the norm-trivial twists with that of the lift remains.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)

universe u v uV uW

/-- At some trace-related pair of additive characters, with self-dual measures,
the certified epsilon monomials of the norm-trivial twists multiply to that of
the lift, up to a constant. -/
def CuspidalSigmaLiftEpsilonComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
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
      ∃ (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E)
        (νF : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances F) ψF)
        (νE : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances E) ψE),
        (∀ x : E, ψE x = ψF (Algebra.trace F E x)) ∧
        ∀ (eF : (Fˣ →* ℂˣ) → ℂˣ × ℤ) (eP : ℂˣ × ℤ),
          (∀ κ ∈ X, IsEpsilonFactorAgainstTrivialCharacter ψF νF.val
            (twist (κ.comp GeneralLinear.determinant) π) (eF κ)) →
          IsEpsilonFactorAgainstTrivialCharacter ψE νE.val P eP →
          EpsilonMonomialProductComparison (LocalFieldData.ofInstances F).residueCardinality
            (LocalFieldData.ofInstances E).residueCardinality X eF eP

/-- The cross-field epsilon comparison implies the exact conductor formula. -/
def CuspidalSigmaLiftConductorFromEpsilonComparisonStatement : Prop :=
  CuspidalSigmaLiftEpsilonComparisonStatement.{u, v, uV, uW} →
    CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorFromEpsilonComparison :
    CuspidalSigmaLiftConductorFromEpsilonComparisonStatement.{u, v, uV, uW} := by
  intro hcomp
  apply cuspidalSigmaLiftConductorFromArbitraryTraceData
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc k V _ _ π hπ hsuper hπirr
    s k₁ hrank W₁ _ _ P₁ hP₁super hP₁irr W _ _ P hP horbit A c hlift f d hf hd X hX
  obtain ⟨ψF, ψE, νF, νE, htrace, hcmp⟩ :=
    hcomp F E σ l hcyc k V π hπ hsuper hπirr s k₁ hrank W₁ P₁ hP₁super hP₁irr
      W P hP horbit A c hlift f d hf hd X hX
  let : FiniteDimensional F E := hcyc.1
  obtain ⟨aF, aOrbit, eF, eOrbit, eP, hF, hOrbit, hprod⟩ :=
    cuspidalSigmaLiftCharZeroEpsilonFactors F E σ k s k₁ hrank π hπirr hsuper P₁ hP₁irr
      hP₁super P horbit X (fun κ hκ => (hX κ).mp hκ) ψF ψE νF νE
  have hnew (i : Fin s) : Conductor.IsNewvectorConductor P₁ (aOrbit i) := by
    let e := σ ^ (i : ℕ)
    exact (Conductor.isNewvectorConductor_comp_fieldEquiv_iff e.toRingEquiv
      (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
      (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap) P₁ (aOrbit i)).mp
      (hOrbit i).2.1
  have hs : 0 < s := by
    by_contra! hs
    have hs0 : s = 0 := by omega
    simp [hs0] at hrank
  let i₀ : Fin s := ⟨0, hs⟩
  refine ⟨ψF, ψE, νF.val, νE.val, aF, aOrbit i₀, eF, eOrbit, eP, htrace, hF, hnew i₀,
    ?_, hprod, hcmp eF eP (fun κ hκ => (hF κ hκ).1) hprod.1⟩
  intro i
  have ha : aOrbit i = aOrbit i₀ := (hnew i).unique (hnew i₀)
  exact ha ▸ hOrbit i

end Langlands.BaseChange
