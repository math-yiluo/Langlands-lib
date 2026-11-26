import Langlands.BaseChange.CharZeroSigmaOrbitIrreducibility
import Langlands.BaseChange.DistinguishedSigmaLiftMatch
import Langlands.BaseChange.DistinguishedStandardEpsilonExponent
import Langlands.BaseChange.DistinguishedTensorLiftTransport

/-! # Identification of the upper distinguished component in the conductor argument -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uK u v uV uW

namespace Langlands.BaseChange

open Automorphic GeneralLinear Global Global.AdelicFunctoriality Global.CompletionPadic
open HarmonicAnalysis LocalClassField
open scoped FiniteExtension

local instance conductorMatchRationalGroup (K : Type uK) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance conductorMatchContinuousGroup (K : Type uK) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance conductorMatchSmoothGroup (K : Type uK) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance conductorMatchFormsGroup (K : Type uK) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance conductorMatchLocalGroup {K : Type uK} [Field K] [NumberField K]
    {n : ℕ} {p : FinitePlace K} (D : LocalRealization K n p) :
    AddCommGroup D.Space := Submodule.addCommGroup _

/-- The upper orbit-product action occurs at the distinguished completion up
to the norm pullback of the lower unramified twist, under uniqueness of local
sigma-lifts and the two supplied lift identities. -/
def DistinguishedConductorLiftIdentificationStatement : Prop :=
  SigmaLiftUniquenessStatement.{u, v, uV, uW, uK} →
  ∀ (K L : Type uK) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (p : FinitePlace K) (w : FinitePlacesAbove L p),
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (a : F ≃+* p.adicCompletion K) (b : E ≃+* w.1.adicCompletion L),
      Continuous a → Continuous a.symm → Continuous b → Continuous b.symm →
      (∀ x : F, b (algebraMap F E x) =
        algebraMap (p.adicCompletion K) (w.1.adicCompletion L) (a x)) →
    ∀ (τ : w.1.adicCompletion L ≃ₐ[p.adicCompletion K] w.1.adicCompletion L),
      (∀ x : E, b (σ x) = τ (b x)) →
    ∀ (k : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (k + 1) F) V)
      (hπ : IsAdmissible π), π.IsIrreducible →
    ∀ (s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
      (W₁ : Type uW) [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
      P₁.IsIrreducible → IsSupercuspidal P₁ →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E) W) (hP : IsAdmissible P),
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
    ∀ (R : Representation ℂ (GeneralLinear (k + 1) (p.adicCompletion K)) V)
      (S : Representation ℂ (GeneralLinear (k + 1) (w.1.adicCompletion L)) W),
      Nonempty (π.Equiv (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) →
      Nonempty (P.Equiv (S.comp (Matrix.GeneralLinearGroup.map b.toRingHom))) →
    ∀ (D : LocalRealization K (k + 1) p) (Q : LocalRealization L (k + 1) w.1)
      (hD : D.IsAdmissible) (hQ : Q.IsAdmissible),
      Q.IsIrreducible → IsLiftAtDistinguishedCompletion w τ l D Q hD hQ →
    ∀ (μ : Quasicharacter (p.adicCompletion K)),
      (padicField p).canonicalTopologicalData.IsUnramifiedCharacter μ.toMonoidHom →
      Nonempty ((twist (μ.toMonoidHom.comp determinant) R).Equiv D.representation) →
      let η := μ.toMonoidHom.comp (normUnits (p.adicCompletion K) (w.1.adicCompletion L))
      (padicField w.1).canonicalTopologicalData.IsUnramifiedCharacter η ∧
        Nonempty ((twist (η.comp determinant) S).Equiv Q.representation)

set_option maxHeartbeats 1750000 in
theorem distinguishedConductorLiftIdentification :
    DistinguishedConductorLiftIdentificationStatement.{uK, u, v, uV, uW} := by
  intro hUnique K L _ _ _ _ _ p w F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc
    a b ha ha' hb hb' hab τ hστ k V _ _ π hπ hπi s k₁ hrank W₁ _ _ P₁ hP₁i hP₁s
    W _ _ P hP ⟨eOrbit⟩ A c hLift R S eπ eP D Q hD hQ hQi hLift' μ hμ eR
  let : FiniteDimensional F E := hcyc.1
  have hPi := isIrreducible_of_sigmaOrbitProduct_equiv σ (Nat.succ_pos k₁) hrank hP₁i hP₁s eOrbit
  let F' := p.adicCompletion K
  let E' := w.1.adicCompletion L
  let : ValuativeRel F' := (topologicalData p).valuativeRel
  let : IsNonarchimedeanLocalField F' := (topologicalData p).localField
  let : ValuativeRel E' := (topologicalData w.1).valuativeRel
  let : IsNonarchimedeanLocalField E' := (topologicalData w.1).localField
  let := LocalFieldTopology.generalLinear_t2Space F' (k + 1)
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F' (k + 1)
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F' (k + 1)
  let := LocalFieldTopology.generalLinear_t2Space E' (k + 1)
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E' (k + 1)
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E' (k + 1)
  obtain ⟨A', c', hL'⟩ := hLift'
  exact ⟨completion_unramified_comp_norm p w μ.toMonoidHom hμ,
    distinguishedSigmaLiftMatch hUnique F E F' E' σ τ l (k + 1) hcyc a b ha ha' hb hb'
      (FiniteExtension.continuous_completionMap p w.1) hab hστ
      V W π P hπi hPi hπ hP A c hLift R S eπ eP μ D.Space Q.Space
      D.representation Q.representation hQi eR hD hQ A' c' hL'⟩

end Langlands.BaseChange
