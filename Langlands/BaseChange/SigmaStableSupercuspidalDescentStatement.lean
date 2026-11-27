import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Classification.Supercuspidal
import Mathlib.RepresentationTheory.Irreducible

/-!
# Descent of σ-stable supercuspidal representations of `GL_n(E)`

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, every σ-stable irreducible supercuspidal representation
`τ` of `GL_n(E)` (`0 < n`), with any isomorphism `A` of `τ` onto `τ^σ`, is a σ-lift of an
irreducible supercuspidal representation `π` of `GL_n(F)` (Henniart–Lemaire 2011, II.4.6 (2) and
II.4.12, Remarque; Arthur–Clozel 1989, Chapter 1, Theorem 6.2 (b)). Statement only; not proved
here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `0 < n`: for every
irreducible supercuspidal representation `τ` of `GL_n(E)` on `W : Type uW` and every
isomorphism `A` of `τ` onto `τ^σ`, there are an irreducible supercuspidal representation `π` of
`GL_n(F)` on some `V : Type uV` and a constant `c` such that `τ` is a σ-lift of `π` with
intertwiner `A` and constant `c` (`IsSigmaLift`, Henniart–Lemaire II.2.7). -/
def SigmaStableSupercuspidalDescentStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 0 < n →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : GeneralLinear.IsSupercuspidal τ),
      τ.IsIrreducible → ∀ A : SigmaIntertwiner σ n τ,
        ∃ (V : Type uV) (_ : AddCommGroup V) (_ : Module ℂ V)
          (π : Representation ℂ (GeneralLinear n F) V) (hπ : GeneralLinear.IsSupercuspidal π)
          (c : ℂ), π.IsIrreducible ∧ IsSigmaLift σ l π hπ.1 τ hτ.1 A c

end Langlands.BaseChange
