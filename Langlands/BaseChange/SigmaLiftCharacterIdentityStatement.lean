import Langlands.BaseChange.TwistedCharacter
import Mathlib.RepresentationTheory.Irreducible

/-!
# σ-lifts are Shintani lifts

The statement that, for irreducible admissible representations `π` of `GL_n(F)` and `τ` of
`GL_n(E)`, a cyclic algebra `E` over a nonarchimedean local field `F` of characteristic zero, an
isomorphism `A` of `τ` onto `τ^σ` and a constant `c`, `τ` is a σ-lift of `π` with constant `c`
(through concordant test functions) exactly when the identity "à la Shintani"
`Θ^A_τ(δ) = c Θ_π(γ)` holds at associated regular points (Henniart–Lemaire 2011, II.2.9,
Proposition). Not proved here.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

/-- For a nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` of
group `⟨σ⟩` of order `l` with its module topology, and `n : ℕ`: for all irreducible admissible
representations `π` of `GL_n(F)` on `V : Type uV` and `τ` of `GL_n(E)` on `W : Type uW`, every
isomorphism `A` of `τ` onto `τ^σ` and every `c : ℂ`, `τ` is a σ-lift of `π` with constant `c`
if and only if the Shintani identity holds with the same constant `c` (Henniart–Lemaire 2011,
II.2.9, Proposition, printed p. 69). -/
def SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      π.IsIrreducible → τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (c : ℂ),
        IsSigmaLift σ l π hπ τ hτ A c ↔ IsShintaniLift σ l π hπ τ hτ A c

end Langlands.BaseChange
