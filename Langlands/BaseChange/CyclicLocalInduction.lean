import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.TwistedCharacter
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Whittaker.GeneralLinear

/-! # Local cyclic induction via base change and determinant twist -/

noncomputable section

universe uK uL uV uW

set_option autoImplicit false

namespace Langlands.BaseChange

variable {K : Type uK} {L : Type uL}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] {r m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The sigma-lift condition in Henniart (2012), Theorem 6. The normalized
product of the entire upstairs orbit is a sigma-lift of the downstairs
action after reindexing its matrices. -/
def HasSigmaOrbitProductLift (σ : L ≃ₐ[K] L) (d : ℕ)
    (π : Representation ℂ (GeneralLinear (r + 1) K) V)
    (τ : Representation ℂ (GeneralLinear (m + 1) L) W) : Prop :=
  ∃ hRank : r + 1 = d * (m + 1),
    let n := d * (m + 1)
    let ρ : Representation ℂ (GeneralLinear n K) V :=
      π.comp (GeneralLinear.reindex (R := K) (finCongr hRank)).symm.toMonoidHom
    let P := sigmaOrbitProduct σ d (Nat.succ_pos m) τ
    have := LocalFieldTopology.generalLinear_t2Space K n
    have := LocalFieldTopology.generalLinear_locallyCompactSpace K n
    have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace K n
    have := LocalFieldTopology.generalLinear_t2Space L n
    have := LocalFieldTopology.generalLinear_locallyCompactSpace L n
    have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace L n
    ∃ (hρ : IsAdmissible ρ) (hP : IsAdmissible P)
      (A : SigmaIntertwiner σ n P) (c : ℂ), IsSigmaLift σ d ρ hρ P hP A c

/-- The local cyclic induction characterization in Henniart (2012), Theorem 6.
Both supplied actions are smooth, generic and unitarizable. The downstairs
action is stable under a determinant twist defining the extension, and its
sigma-lift is the normalized product of the entire upstairs orbit. -/
def IsCyclicLocalInductionOf (σ : L ≃ₐ[K] L) (d : ℕ)
    (π : Representation ℂ (GeneralLinear (r + 1) K) V)
    (τ : Representation ℂ (GeneralLinear (m + 1) L) W) : Prop :=
  IsSmooth π ∧ IsUnitarizable π ∧
    (∃ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter K, Whittaker.IsGeneric ψ r π) ∧
  IsSmooth τ ∧ IsUnitarizable τ ∧
    (∃ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter L, Whittaker.IsGeneric ψ m τ) ∧
  (∃ κ : Kˣ →* ℂˣ, Continuous κ ∧
    κ.ker = MonoidHom.range (Units.map (Algebra.norm K : L →* K)) ∧
    Nonempty (π.Equiv (twist (κ.comp GeneralLinear.determinant) π))) ∧
  HasSigmaOrbitProductLift σ d π τ

end Langlands.BaseChange
