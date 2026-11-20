import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Mathlib.RepresentationTheory.Irreducible

/-!
# Descent of σ-discrete series

Henniart–Lemaire (2011), II.4.6, Théorème (2), first assertion: every σ-discrete series of
`GL_n(E)` is the σ-lift of a discrete series of `GL_n(F)` (Arthur–Clozel (1989), Chapter 1,
Theorem 6.2 (b) in the discrete case, §6.3).
-/

namespace Langlands.BaseChange

/-- Descent of σ-discrete series (Henniart–Lemaire 2011, II.4.6, Théorème (2), first
assertion). For a nonarchimedean local field `F` of characteristic zero and a cyclic field
extension `E/F` of degree `l` with generator `σ`: for every σ-discrete series `ρ` of `GL_n(E)`
and every intertwiner `A` of `ρ` with `ρ^σ`, there are an irreducible admissible
square-integrable representation `π` of `GL_n(F)`, on a space in `Type uV`, and a constant `c`
such that `ρ` is a σ-lift of `π` for `A` and `c`. -/
def SigmaDiscreteDescentStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l),
    haveI : Module.Finite F E := hσ.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear n E) W) (hρ : IsAdmissible ρ),
      IsSigmaDiscreteSeries σ n ρ → ∀ A : SigmaIntertwiner σ n ρ,
      ∃ (V : Type uV) (_ : AddCommGroup V) (_ : Module ℂ V)
        (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π) (c : ℂ),
        π.IsIrreducible ∧ JacquetLanglands.IsSquareIntegrable π ∧
          IsSigmaLift σ l π hπ ρ hρ A c

end Langlands.BaseChange
