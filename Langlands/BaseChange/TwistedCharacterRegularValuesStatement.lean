import Langlands.BaseChange.TwistedCharacter
import Mathlib.RepresentationTheory.Irreducible

/-!
# Twisted characters have values at σ-regular elements

The statement that the twisted character of an irreducible admissible representation of
`GL_n(E)`, for a cyclic algebra `E` over a nonarchimedean local field `F` of characteristic zero,
has a value at every σ-regular element (Henniart–Lemaire 2011, II.2.8; Arthur–Clozel 1989,
Chapter 1, Proposition 2.2). It is the twisted analogue of
`Langlands.JacquetLanglands.HasRegularSemisimpleCharacterValues`. Not proved here.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

/-- For a nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` of
group `⟨σ⟩` of order `l` with its module topology, and `n : ℕ`: for every irreducible admissible
representation `τ` of `GL_n(E)` on a complex vector space `W : Type uW`, every isomorphism `A` of
`τ` onto `τ^σ` and every σ-regular `δ ∈ GL_n(E)`, the twisted character `Θ^A_τ` has a value at
`δ` (Henniart–Lemaire 2011, II.2.8, printed pp. 67–69). -/
def TwistedCharacterRegularValuesStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ), τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (δ : GeneralLinear n E), IsSigmaRegular σ l δ →
        ∃ c : ℂ, HasTwistedCharacterValue τ hτ A.toLinearMap δ c

end Langlands.BaseChange
