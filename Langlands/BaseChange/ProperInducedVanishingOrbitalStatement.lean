import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter

/-!
# Test functions killing properly induced twisted traces have σ-elliptic orbital integrals

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, a Schwartz–Bruhat function `φ` on `GL_{r+1}(E)` whose
twisted traces vanish on every irreducible representation induced from an irreducible
admissible σ-stable representation of a proper standard Levi subgroup has σ-orbital integrals
vanishing at every σ-regular element that is not σ-elliptic. This is the argument of
Henniart–Lemaire 2011, II.5.14, proof of Proposition 2 (2), printed pp. 116–117 (descent of
twisted orbital integrals, the twisted density theorem II.5.14, Proposition 1 (2), on the Levi
subgroup, and descent of twisted characters), and of Arthur–Clozel 1989, Chapter 1,
Lemma 2.12 (ii), printed p. 19, with the descent argument of Proposition 2.7, printed
pp. 15–17. Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis GeneralLinear

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `r : ℕ`: for every
Haar measure `μ` on `GL_{r+1}(E)` (Borel σ-algebra) and every Schwartz–Bruhat function `φ` on
`GL_{r+1}(E)` such that, for every standard block shape `B` with at least two blocks and
every irreducible admissible σ-stable representation `Ξ` of the Levi product of `B` (carrier
in universe `uW`) whose unnormalized smooth induction `Ind_B(Ξ)` from the standard upper
block parabolic subgroup is irreducible, `tr(Ind_B(Ξ)(φ) ∘ A') = 0` for every admissibility
proof and every isomorphism `A'` of `Ind_B(Ξ)` onto its σ-conjugate, the σ-orbital integrals
of `φ` vanish at every σ-regular element that is not σ-elliptic, for every right Haar measure
on its σ-centralizer and every compatible quotient measure (Henniart–Lemaire 2011, II.5.14,
proof of Proposition 2 (2); Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (ii)). -/
def ProperInducedVanishingOrbitalStatement.{u, v, uW} : Prop :=
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
    ∀ (μ : Measure (GeneralLinear (r + 1) E)) [μ.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear (r + 1) E)),
      (∀ B : BlockShape (r + 1), 2 ≤ B.length →
        ∀ (X : Type uW) [AddCommGroup X] [Module ℂ X]
          (Ξ : Representation ℂ (B.Levi E) X),
          IsAdmissible Ξ → Ξ.IsIrreducible → IsLeviSigmaStable σ B Ξ →
          (Induction.smoothInduced (B.parabolic E)
            (Ξ.comp (B.leviProjection E))).IsIrreducible →
          ∀ (h : IsAdmissible
              (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))
            (A' : SigmaIntertwiner σ (r + 1)
              (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))),
            twistedDistribution μ
              (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))) h
              A'.toLinearMap φ = 0) →
        SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ

end Langlands.BaseChange
