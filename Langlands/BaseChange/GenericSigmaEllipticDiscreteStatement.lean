import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter
import Langlands.HarmonicAnalysis.Basic
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# A generic σ-stable representation detected on the σ-elliptic set is a σ-discrete series

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, a generic representation `τ` of `GL_{r+1}(E)` with
unitary central character and an isomorphism `A` of `τ` onto `τ^σ`, whose twisted
distribution character `φ ↦ tr(τ(φ) ∘ A)` is nonzero on some Schwartz–Bruhat function whose
σ-orbital integrals vanish off the σ-elliptic set, is a σ-discrete series representation.
This is the twisted form of Henniart–Lemaire 2011, II.5.8, Lemme (printed p. 106), as used in
II.5.15, Proposition 1 (printed p. 117), and of Arthur–Clozel 1989, Chapter 1, Lemma 2.11
(printed pp. 18–19). Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `r : ℕ`: let `τ` be an
admissible representation of `GL_{r+1}(E)` on `W : Type uW` that is generic for some unitary
additive character `ψ` of `E` (`Whittaker.IsGeneric`, which includes irreducibility), with a
central character `χ` of absolute value `1`, let `A` be an isomorphism of `τ` onto `τ^σ` and
`μ` a Haar measure on `GL_{r+1}(E)` (Borel σ-algebra). If some Schwartz–Bruhat function `φ`
whose σ-orbital integrals vanish at every σ-regular element that is not σ-elliptic has
`tr(τ(φ) ∘ A) ≠ 0`, then `τ` is a σ-discrete series representation (Henniart–Lemaire 2011,
II.5.8 and II.5.15, Proposition 1; Arthur–Clozel 1989, Chapter 1, Lemma 2.11). -/
def GenericSigmaEllipticDiscreteStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l r : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E (r + 1)
    haveI := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
    letI : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
    haveI : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear (r + 1) E) W) (hτ : IsAdmissible τ)
      (ψ : UnitaryAdditiveCharacter E), Whittaker.IsGeneric ψ r τ →
      ∀ χ : Subgroup.center (GeneralLinear (r + 1) E) →* ℂˣ, HasCentralCharacterRep τ χ →
        (∀ z, ‖(χ z : ℂ)‖ = 1) →
      ∀ (A : SigmaIntertwiner σ (r + 1) τ) (μ : Measure (GeneralLinear (r + 1) E))
        [μ.IsHaarMeasure] (φ : SchwartzBruhat (GeneralLinear (r + 1) E)),
        SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ →
        twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0 →
        IsSigmaDiscreteSeries σ (r + 1) τ

end Langlands.BaseChange
