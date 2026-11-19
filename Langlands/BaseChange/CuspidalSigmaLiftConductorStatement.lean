import Langlands.BaseChange.ExtensionInvariants
import Langlands.BaseChange.Norm
import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.Representation.Conductor.Definitions
import Langlands.Representation.Twist.Definitions
import Langlands.Group.GL.LocalFieldTopology

/-!
# Conductor identity for a cuspidal sigma-lift

The proposition giving the conductor form of Arthur–Clozel, Chapter 1,
Proposition 6.9(ii).
-/

noncomputable section

namespace Langlands.BaseChange

universe u v uV uW

/-- The conductor identity for a sigma-lift expressed as a supercuspidal orbit product. -/
def CuspidalSigmaLiftConductorStatement : Prop :=
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
      ∑ κ ∈ X, Conductor.firstFixedLevel (twist (κ.comp GeneralLinear.determinant) π) =
        (f : WithTop ℕ) * ((s : WithTop ℕ) * Conductor.firstFixedLevel P₁ +
          ((k + 1 : ℕ) : WithTop ℕ) * (d : WithTop ℕ))

end Langlands.BaseChange
