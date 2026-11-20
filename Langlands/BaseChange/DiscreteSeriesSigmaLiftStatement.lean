import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Mathlib.RepresentationTheory.Irreducible

/-!
# Existence of σ-lifts of essentially discrete series

Henniart–Lemaire (2011), II.4.6, Théorème (1), extended to essentially discrete
representations in II.4.7: every irreducible essentially square-integrable representation of
`GL_n(F)` has an irreducible σ-lift to `GL_n(E)`, which is a σ-discrete series when the
representation is square-integrable (Arthur–Clozel (1989), Chapter 1, Theorem 6.2 (a) in the
discrete case, §6.3, with Lemma 2.11).
-/

namespace Langlands.BaseChange

/-- Existence of σ-lifts of essentially discrete series (Henniart–Lemaire 2011, II.4.6,
Théorème (1), and II.4.7). For a nonarchimedean local field `F` of characteristic zero and a
cyclic field extension `E/F` of degree `l` with generator `σ`: every irreducible admissible
essentially square-integrable representation `π` of `GL_n(F)` has a σ-lift `ρ`, an irreducible
admissible representation of `GL_n(E)` on a space in `Type uW`, for some intertwiner `A` and
constant `c`; if `π` is square-integrable, `ρ` is a σ-discrete series. -/
def DiscreteSeriesSigmaLiftStatement.{u, v, uV, uW} : Prop :=
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
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π),
      π.IsIrreducible → JacquetLanglands.IsEssentiallySquareIntegrable π →
      ∃ (W : Type uW) (_ : AddCommGroup W) (_ : Module ℂ W)
        (ρ : Representation ℂ (GeneralLinear n E) W) (hρ : IsAdmissible ρ)
        (A : SigmaIntertwiner σ n ρ) (c : ℂ),
        ρ.IsIrreducible ∧ IsSigmaLift σ l π hπ ρ hρ A c ∧
          (JacquetLanglands.IsSquareIntegrable π → IsSigmaDiscreteSeries σ n ρ)

end Langlands.BaseChange
