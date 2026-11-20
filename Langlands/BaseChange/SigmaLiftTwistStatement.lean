import Langlands.BaseChange.Norm
import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Twist.Definitions
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.RingTheory.Norm.Basic

/-!
# Compatibility of sigma-lifts with character twists

The admissible distributional form of Henniart--Lemaire II.2.9, Remark (4).
-/

namespace Langlands.BaseChange

universe u v uV uW

/-- Twisting both sides of a sigma-lift by corresponding norm characters preserves
the lift and its constant, with the same underlying intertwining operator. -/
def SigmaLiftTwistStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (hcyclic : IsCyclicAlgebra σ l),
    haveI : Module.Finite F E := hcyclic.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ)
      (A : SigmaIntertwiner σ n τ) (c : ℂ)
      (ω : Fˣ →* ℂˣ),
      Continuous (fun x : Fˣ => (ω x : ℂ)) →
      let ωE : Eˣ →* ℂˣ :=
        ω.comp (Units.map (Algebra.norm F : E →* F))
      let πω := twist (ω.comp GeneralLinear.determinant) π
      let τω := twist (ωE.comp GeneralLinear.determinant) τ
      ∀ (hπω : IsAdmissible πω) (hτω : IsAdmissible τω)
        (Aω : SigmaIntertwiner σ n τω),
        (Aω : W → W) = (A : W → W) →
        IsSigmaLift σ l π hπ τ hτ A c →
        IsSigmaLift σ l πω hπω τω hτω Aω c

end Langlands.BaseChange
