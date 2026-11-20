import Langlands.BaseChange.TwistedCharacter
import Mathlib.RepresentationTheory.Irreducible

/-!
# Uniqueness of σ-lifts

Henniart–Lemaire (2011), II.2.9, Remarque (2): an irreducible admissible representation of
`GL_n(F)` has, up to isomorphism, at most one irreducible σ-lift to `GL_n(E)`
(Arthur–Clozel (1989), Chapter 1, Theorem 6.2 (a), "unique lift", with Lemma 6.3).
-/

namespace Langlands.BaseChange

/-- Uniqueness of σ-lifts (Henniart–Lemaire 2011, II.2.9, Remarque (2)). For a nonarchimedean
local field `F` of characteristic zero, a cyclic `F`-algebra `E` of group `⟨σ⟩` of order `l`,
and an irreducible admissible representation `π` of `GL_n(F)`: if irreducible admissible
representations `ρ` and `ρ'` of `GL_n(E)` are σ-lifts of `π`, for some intertwiners `A`, `A'`
and constants `c`, `c'`, then `ρ` and `ρ'` are isomorphic. -/
def SigmaLiftUniquenessStatement.{u, v, uV, uW, uW'} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l),
    haveI : Module.Finite F E := hσ.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π), π.IsIrreducible →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear n E) W) (hρ : IsAdmissible ρ), ρ.IsIrreducible →
    ∀ {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
      (ρ' : Representation ℂ (GeneralLinear n E) W') (hρ' : IsAdmissible ρ'),
      ρ'.IsIrreducible →
    ∀ (A : SigmaIntertwiner σ n ρ) (A' : SigmaIntertwiner σ n ρ') (c c' : ℂ),
      IsSigmaLift σ l π hπ ρ hρ A c → IsSigmaLift σ l π hπ ρ' hρ' A' c' →
        Nonempty (ρ.Equiv ρ')

end Langlands.BaseChange
