import Langlands.BaseChange.TwistedCharacter
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Mathlib.RepresentationTheory.Irreducible

/-!
# Independence of σ-lifts of essentially discrete series from the generator

Henniart–Lemaire (2011), II.4.6, Théorème (3), extended to essentially discrete
representations in II.4.7: for essentially square-integrable representations of `GL_n(F)`,
the notion of σ-lift to `GL_n(E)` does not depend on the choice of the generator `σ` of
`Gal(E/F)` (Arthur–Clozel (1989), Chapter 1, Theorem 6.2 (c), for tempered representations).
A statement only.
-/

namespace Langlands.BaseChange

/-- Independence of σ-lifts of essentially discrete series from the generator
(Henniart–Lemaire 2011, II.4.6, Théorème (3), and II.4.7). For a nonarchimedean local field
`F` of characteristic zero, a cyclic field extension `E/F` of degree `l`, and two generators
`σ` and `σ'` of `Gal(E/F)`: if an irreducible admissible representation `ρ` of `GL_n(E)` is a
σ-lift of an irreducible admissible essentially square-integrable representation `π` of
`GL_n(F)`, for some σ-intertwiner `A` and constant `c`, then `ρ` is a σ'-lift of `π` for some
σ'-intertwiner `A'` and constant `c'`. -/
def SigmaLiftGeneratorIndependenceStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ σ' : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l),
    IsCyclicAlgebra σ' l →
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
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear n E) W) (hρ : IsAdmissible ρ), ρ.IsIrreducible →
    ∀ (A : SigmaIntertwiner σ n ρ) (c : ℂ), IsSigmaLift σ l π hπ ρ hρ A c →
      ∃ (A' : SigmaIntertwiner σ' n ρ) (c' : ℂ), IsSigmaLift σ' l π hπ ρ hρ A' c'

end Langlands.BaseChange
