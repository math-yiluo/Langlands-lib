import Langlands.BaseChange.SigmaDiscreteRegularDescentStatement
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Square-integrability of a generic unitarizable regular σ-descent

This module states a local criterion for the square-integrability of a regular
σ-descent. It combines the elliptic character argument of Henniart–Lemaire
(2011), II.4.5 and II.4.8, with Arthur–Clozel (1989), Chapter 1, Lemmas 2.11–2.12
and §6.3. The paired Markdown explains the role of the regular support conditions.
-/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands HarmonicAnalysis

/-- Let `E/F` be a cyclic extension of any degree over a nonarchimedean local
field `F` of characteristic zero. If `π` on `GL_{r+1}(F)` is generic and
unitarizable and satisfies `IsRegularSigmaLift` with a σ-discrete series `ρ` on
`GL_{r+1}(E)` and a σ-intertwiner `A`, then `π` is square-integrable modulo the
center. -/
def RegularSigmaLiftSquareIntegrableStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l r : ℕ) (hσ : IsCyclicAlgebra σ l),
    haveI : Module.Finite F E := hσ.1
    haveI := LocalFieldTopology.generalLinear_t2Space F (r + 1)
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (r + 1)
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (r + 1)
    haveI := generalLinear_t2Space_of_finite F E (r + 1)
    haveI := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear (r + 1) E) W) (hρ : IsAdmissible ρ),
      IsSigmaDiscreteSeries σ (r + 1) ρ → ∀ A : SigmaIntertwiner σ (r + 1) ρ,
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (GeneralLinear (r + 1) F) V) (hπ : IsAdmissible π)
        (ψ : UnitaryAdditiveCharacter F),
        Whittaker.IsGeneric ψ r π → IsUnitarizable π →
        ∀ c : ℂ, IsRegularSigmaLift σ l π hπ ρ hρ A c →
          JacquetLanglands.IsSquareIntegrable π

end Langlands.BaseChange
