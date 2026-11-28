import Langlands.BaseChange.EllipticSupport
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter

/-!
# Twisted traces of σ-stable proper inductions vanish on the σ-elliptic set

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, an irreducible admissible representation `τ` of
`GL_n(E)` that is isomorphic to the smooth induction, from the standard upper block parabolic
of a block shape with at least two blocks, of a smooth σ-stable representation of the Levi
product has twisted distribution character `φ ↦ tr(τ(φ) ∘ A)` equal to zero on every
Schwartz–Bruhat function supported in the σ-elliptic set, for every isomorphism `A` of `τ` onto
`τ^σ`. This is the consequence of the twisted induced-character formula of Henniart–Lemaire
2011, II.4.5 (printed pp. 86–88), used in the proof of II.5.8, Lemme (printed p. 106).
Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis Langlands.GeneralLinear

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `n : ℕ`: let `τ` be an
irreducible admissible representation of `GL_n(E)` on `W : Type uW`, `B` a block shape of `n`
with at least two blocks and `Ξ` a smooth representation of the Levi product of `B` on
`X : Type uW` with `Ξ ≅ Ξ^σ` (`IsLeviSigmaStable`), such that `τ` is isomorphic to the
unnormalized smooth induction of `Ξ`, inflated through the Levi projection, from the standard
upper block parabolic of `B`. Then for every isomorphism `A` of `τ` onto `τ^σ`, every Haar
measure `μ` on `GL_n(E)` (Borel σ-algebra) and every Schwartz–Bruhat function `φ` vanishing off
the σ-elliptic set, `tr(τ(φ) ∘ A) = 0` (Henniart–Lemaire 2011, II.4.5 (3) and its consequence
in the proof of II.5.8, Lemme). -/
def SigmaInducedEllipticVanishingStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ), τ.IsIrreducible →
      ∀ (B : BlockShape n), 2 ≤ B.length →
      ∀ (X : Type uW) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
        IsSmooth Ξ → IsLeviSigmaStable σ B Ξ →
        Nonempty (τ.Equiv
          (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))) →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
        (φ : SchwartzBruhat (GeneralLinear n E)),
        IsSigmaEllipticSupported σ l ⇑φ →
        twistedDistribution μ τ hτ A.toLinearMap φ = 0

end Langlands.BaseChange
