import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.Whittaker.GeneralLinear
import Mathlib.RepresentationTheory.Irreducible

/-!
# Fibres of local cyclic base change at an essentially square-integrable representation

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero, if an irreducible generic representation `π'` of `GL_{r+1}(F)` has the same
irreducible σ-lift `τ` as an irreducible essentially square-integrable representation `π`, then
`π'` is isomorphic to `(κ ∘ det) ⊗ π` for a character `κ` of `Fˣ` trivial on the norms
`N_{E/F}(Eˣ)` (Henniart–Lemaire 2011, II.4.8, Lemme (2)). Not proved here.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, `r : ℕ` and a unitary additive
character `ψ` of `F`: if `π` is an irreducible admissible essentially square-integrable
representation of `GL_{r+1}(F)` on `V : Type uV`, `π'` an admissible representation of
`GL_{r+1}(F)` on `V' : Type uV'` that is generic for `ψ`, and `τ` an irreducible admissible
representation of `GL_{r+1}(E)` on `W : Type uW` that is a σ-lift of both `π` and `π'` (through
any intertwiners `A`, `A'` and constants `c`, `c'`), then `π'` is isomorphic to the twist of `π`
by `κ ∘ det` for a character `κ` of `Fˣ` trivial on `N_{E/F}(Eˣ)` (Henniart–Lemaire 2011,
II.4.8, Lemme (2), printed p. 90). -/
def SigmaLiftGenericFibreStatement.{u, v, uV, uV', uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l r : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F (r + 1)
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (r + 1)
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (r + 1)
    haveI := generalLinear_t2Space_of_finite F E (r + 1)
    haveI := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
    ∀ (ψ : UnitaryAdditiveCharacter F)
      {V : Type uV} [AddCommGroup V] [Module ℂ V] {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear (r + 1) F) V) (hπ : IsAdmissible π)
      (π' : Representation ℂ (GeneralLinear (r + 1) F) V') (hπ' : IsAdmissible π')
      (τ : Representation ℂ (GeneralLinear (r + 1) E) W) (hτ : IsAdmissible τ),
      π.IsIrreducible → IsEssentiallySquareIntegrable π →
      Whittaker.IsGeneric ψ r π' → τ.IsIrreducible →
      ∀ (A A' : SigmaIntertwiner σ (r + 1) τ) (c c' : ℂ),
        IsSigmaLift σ l π hπ τ hτ A c → IsSigmaLift σ l π' hπ' τ hτ A' c' →
        ∃ κ : Fˣ →* ℂˣ, IsNormTrivial E κ ∧
          Nonempty (π'.Equiv (twist (κ.comp GeneralLinear.determinant) π))

end Langlands.BaseChange
