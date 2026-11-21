import Langlands.BaseChange.DeterminantTwistFieldEquiv
import Langlands.BaseChange.SigmaLiftFieldEquivTransport
import Langlands.BaseChange.SigmaLiftNormTwist
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.SigmaLiftUniquenessStatement
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport
import Langlands.Representation.Induction.BinaryProduct

/-! # Identification of the distinguished sigma-lift after globalization -/

noncomputable section

set_option autoImplicit false

universe u v u' v' uV uW uV' uW'

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis LocalClassField

/-- Under the exact uniqueness proposition, a second local sigma-lift on
compatible field realizations is the norm twist of the original upper
representation if its lower component is the corresponding determinant twist. -/
def DistinguishedSigmaLiftMatchStatement : Prop :=
  SigmaLiftUniquenessStatement.{u, v, uV, uW, uW'} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (F' : Type u') [Field F'] [TopologicalSpace F'] [IsTopologicalRing F']
    (E' : Type v') [Field E'] [TopologicalSpace E'] [IsTopologicalRing E'] [Algebra F' E']
    [FiniteDimensional F' E']
    (σ : E ≃ₐ[F] E) (τ : E' ≃ₐ[F'] E') (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ (a : F ≃+* F') (b : E ≃+* E'), Continuous a → Continuous a.symm →
      Continuous b → Continuous b.symm → Continuous (algebraMap F' E') →
      (∀ x, b (algebraMap F E x) = algebraMap F' E' (a x)) →
      (∀ x, b (σ x) = τ (b x)) →
    ∀ [T2Space (GeneralLinear n F')] [LocallyCompactSpace (GeneralLinear n F')]
      [TotallyDisconnectedSpace (GeneralLinear n F')]
      [T2Space (GeneralLinear n E')] [LocallyCompactSpace (GeneralLinear n E')]
      [TotallyDisconnectedSpace (GeneralLinear n E')],
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := LocalFieldTopology.generalLinear_t2Space E n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (P : Representation ℂ (GeneralLinear n E) W),
      π.IsIrreducible → P.IsIrreducible →
    ∀ (hπ : IsAdmissible π) (hP : IsAdmissible P) (A : SigmaIntertwiner σ n P) (c : ℂ),
      IsSigmaLift σ l π hπ P hP A c →
    ∀ (R : Representation ℂ (GeneralLinear n F') V) (S : Representation ℂ (GeneralLinear n E') W),
      Nonempty (π.Equiv (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) →
      Nonempty (P.Equiv (S.comp (Matrix.GeneralLinearGroup.map b.toRingHom))) →
    ∀ (μ : Quasicharacter F') (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (W' : Type uW') [AddCommGroup W'] [Module ℂ W']
      (π' : Representation ℂ (GeneralLinear n F') V') (P' : Representation ℂ (GeneralLinear n E') W'),
      P'.IsIrreducible →
      Nonempty ((twist (μ.toMonoidHom.comp determinant) R).Equiv π') →
    ∀ (hπ' : IsAdmissible π') (hP' : IsAdmissible P') (A' : SigmaIntertwiner τ n P') (c' : ℂ),
      IsSigmaLift τ l π' hπ' P' hP' A' c' →
      Nonempty ((twist ((μ.toMonoidHom.comp (normUnits F' E')).comp determinant) S).Equiv P')

set_option maxHeartbeats 2000000 in
/-- Pull back the second sigma-lift, twist the original one, and apply uniqueness
on the original extension. Surjectivity of the upper field map transports the
resulting intertwiner to the second realization. -/
theorem distinguishedSigmaLiftMatch : DistinguishedSigmaLiftMatchStatement.{u, v, u', v', uV, uW, uV', uW'} := by
  intro hUnique F _ _ _ _ _ E _ _ _ _ _ _ F' _ _ _ E' _ _ _ _ _
    σ τ l n hcyc a b ha ha' hb hb' hmap' hab hστ _ _ _ _ _ _
    V _ _ W _ _ π P hiπ hiP hπ hP A c hL R S ⟨eR⟩ ⟨eS⟩ μ V' _ _ W' _ _
    π' P' hiP' ⟨eπ'⟩ hπ' hP' A' c' hL'
  let : Module.Finite F E := hcyc.1
  let := LocalFieldTopology.generalLinear_t2Space F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let := LocalFieldTopology.generalLinear_t2Space E n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
  let aG := fieldEquiv n a ha ha'
  let bG := fieldEquiv n b hb hb'
  let aU := Units.mapEquiv a.toMulEquiv
  let bU := Units.mapEquiv b.toMulEquiv
  have hmap : Continuous (algebraMap F E) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)
  obtain ⟨hπ₁, hP₁, A₁, -, hL₁⟩ :=
    sigmaLiftFieldEquivTransport F E F' E' n l a b ha ha' hb hb' hmap hmap' hab σ τ hστ
      π' P' hπ' hP' A' c' hL'
  let ω : Quasicharacter F := ⟨μ.toMonoidHom.comp aU.toMonoidHom,
    μ.continuous.comp (ha.units_map a.toMonoidHom)⟩
  obtain ⟨hπω, hPω, Aω, -, hLω⟩ :=
    sigmaLiftFieldTwist F E σ l n hcyc V W π hπ P hP A c hL ω
  let πω := twist (ω.toMonoidHom.comp determinant) π
  let Pω := twist ((ω.toMonoidHom.comp (normUnits F E)).comp determinant) P
  let dF : πω.Equiv (π'.comp aG.toMonoidHom) :=
    (pullbackDeterminantTwistEquiv a eR μ.toMonoidHom).trans (BinaryTensor.compEquiv eπ' aG.toMonoidHom)
  have hL₂ := hL₁.transport hπω dF.symm hP₁ (Representation.Equiv.refl _)
  have hiω : πω.IsIrreducible := (isIrreducible_twist_iff _ π).2 hiπ
  have hiPω : Pω.IsIrreducible := (isIrreducible_twist_iff _ P).2 hiP
  have hiP₁ : Representation.IsIrreducible (P'.comp bG.toMonoidHom) :=
    (isIrreducible_comp_continuousMulEquiv_iff P' bG).2 hiP'
  obtain ⟨dP⟩ := hUnique F E σ l n hcyc πω hπω hiω Pω hPω hiPω
    (P'.comp bG.toMonoidHom) hP₁ hiP₁ Aω (A₁.transport (Representation.Equiv.refl _)) c c' hLω hL₂
  let ν := μ.toMonoidHom.comp (normUnits F' E')
  have hn : ν.comp bU.toMonoidHom = ω.toMonoidHom.comp (normUnits F E) := by
    apply MonoidHom.ext
    intro x
    exact congrArg μ (FiniteArtinTransport.normUnits_map a b (RingHom.ext fun x => (hab x).symm) x)
  let dB := pullbackDeterminantTwistEquiv b eS ν
  have dB' : Pω.Equiv ((twist (ν.comp determinant) S).comp bG.toMonoidHom) := by
    unfold Pω
    rw [← hn]
    exact dB
  let d := dB'.symm.trans dP
  refine ⟨Representation.Equiv.mk d.toLinearEquiv fun g => ?_⟩
  obtain ⟨x, rfl⟩ := bG.surjective g
  exact d.isIntertwining' x

end Langlands.BaseChange
