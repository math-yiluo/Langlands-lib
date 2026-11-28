import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# A generic σ-stable representation that is not σ-induced is tempered

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, a generic σ-stable representation `τ` of
`GL_{r+1}(E)` with unitary central character that is not isomorphic to the smooth induction,
from a proper standard block parabolic, of a smooth σ-stable representation of its Levi product
is tempered. It isolates the classification step of the proof of Henniart–Lemaire 2011, II.5.8,
Lemme (printed p. 106), with II.5.15, Proposition 1 (printed p. 117), and of Arthur–Clozel
1989, Chapter 1, Lemma 2.11 (printed pp. 18–19). Statement only; not proved here. See the
paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis Langlands.GeneralLinear

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `r : ℕ`: let `τ` be an
admissible representation of `GL_{r+1}(E)` on `W : Type uW` that is generic for some unitary
additive character `ψ` of `E` (`Whittaker.IsGeneric`, which includes irreducibility), with a
central character `χ` of absolute value `1`, and σ-stable (`τ ≅ τ^σ`). Suppose that for every
block shape `B` of `r + 1` with at least two blocks and every smooth representation `Ξ` of the
Levi product of `B` on a space `X : Type uW` with `Ξ ≅ Ξ^σ` (`IsLeviSigmaStable`), `τ` is not
isomorphic to the unnormalized smooth induction of `Ξ`, inflated through the Levi projection,
from the standard upper block parabolic of `B`. Then `τ` is tempered (`IsTemperedRep`). -/
def GenericSigmaNoninducedTemperedStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l r : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E (r + 1)
    haveI := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear (r + 1) E) W), IsAdmissible τ →
      ∀ (ψ : UnitaryAdditiveCharacter E), Whittaker.IsGeneric ψ r τ →
      ∀ χ : Subgroup.center (GeneralLinear (r + 1) E) →* ℂˣ, HasCentralCharacterRep τ χ →
        (∀ z, ‖(χ z : ℂ)‖ = 1) → IsSigmaStable σ (r + 1) τ →
        (∀ B : BlockShape (r + 1), 2 ≤ B.length →
          ∀ (X : Type uW) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
            IsSmooth Ξ → IsLeviSigmaStable σ B Ξ →
              IsEmpty (τ.Equiv
                (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))) →
        IsTemperedRep τ

end Langlands.BaseChange
