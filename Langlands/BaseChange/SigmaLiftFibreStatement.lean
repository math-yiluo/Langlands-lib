import Langlands.BaseChange.Norm
import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.Twist.Definitions
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.RingTheory.Norm.Basic

/-!
# Fibres of local cyclic base change for essentially discrete series

The essentially square-integrable specialization of
Henniart--Lemaire II.4.8, Lemma (2).
-/

namespace Langlands.BaseChange

universe u v uV uV' uW

/-- Two irreducible essentially square-integrable representations with a
common sigma-lift differ by a character trivial on norms. -/
def SigmaLiftFibreStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
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
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (π' : Representation ℂ (GeneralLinear n F) V') (hπ' : IsAdmissible π')
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      π.IsIrreducible → π'.IsIrreducible → τ.IsIrreducible →
      JacquetLanglands.IsEssentiallySquareIntegrable π →
      JacquetLanglands.IsEssentiallySquareIntegrable π' →
      ∀ (A A' : SigmaIntertwiner σ n τ) (c c' : ℂ),
        IsSigmaLift σ l π hπ τ hτ A c →
        IsSigmaLift σ l π' hπ' τ hτ A' c' →
        ∃ κ : Fˣ →* ℂˣ,
          (∀ x : Eˣ, κ (Units.map (Algebra.norm F : E →* F) x) = 1) ∧
          Nonempty (π'.Equiv (twist (κ.comp GeneralLinear.determinant) π))

end Langlands.BaseChange
