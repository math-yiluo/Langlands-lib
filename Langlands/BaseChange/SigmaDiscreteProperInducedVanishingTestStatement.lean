import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter

/-!
# σ-discrete series are detected by test functions killing properly induced twisted traces

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, every σ-discrete series representation `τ` of
`GL_{r+1}(E)`, with an isomorphism `A` of `τ` onto `τ^σ` and a Haar measure `μ`, has a
Schwartz–Bruhat test function `φ` with `tr(τ(φ) ∘ A) ≠ 0` whose twisted traces vanish on
every irreducible representation induced from an irreducible admissible σ-stable
representation of a proper standard Levi subgroup. The compactly supported function `φ̃` of
Henniart–Lemaire's construction of twisted pseudo-coefficients is such a function
(Henniart–Lemaire 2011, II.5.13, Proposition, its proof and Remarque, and II.5.14,
Proposition 2 (1) and its proof, printed pp. 113–116). Statement only; not proved here. See
the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis GeneralLinear

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `r : ℕ`: for every
σ-discrete series representation `τ` of `GL_{r+1}(E)` on `W : Type uW` (admissible), every
isomorphism `A` of `τ` onto `τ^σ` and every Haar measure `μ` on `GL_{r+1}(E)` (Borel
σ-algebra), some Schwartz–Bruhat function `φ` satisfies `tr(τ(φ) ∘ A) ≠ 0`, and for every
standard block shape `B` with at least two blocks and every irreducible admissible σ-stable
representation `Ξ` of the Levi product of `B` (carrier in universe `uW`) whose unnormalized
smooth induction `Ind_B(Ξ)` from the standard upper block parabolic subgroup is irreducible,
`tr(Ind_B(Ξ)(φ) ∘ A') = 0` for every admissibility proof and every isomorphism `A'` of
`Ind_B(Ξ)` onto its σ-conjugate (Henniart–Lemaire 2011, II.5.13, Proposition and Remarque,
and II.5.14, Proposition 2 (1)). -/
def SigmaDiscreteProperInducedVanishingTestStatement.{u, v, uW} : Prop :=
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
      (τ : Representation ℂ (GeneralLinear (r + 1) E) W) (hτ : IsAdmissible τ),
      IsSigmaDiscreteSeries σ (r + 1) τ →
      ∀ (A : SigmaIntertwiner σ (r + 1) τ) (μ : Measure (GeneralLinear (r + 1) E))
        [μ.IsHaarMeasure],
        ∃ φ : SchwartzBruhat (GeneralLinear (r + 1) E),
          twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0 ∧
          ∀ B : BlockShape (r + 1), 2 ≤ B.length →
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
                  A'.toLinearMap φ = 0

end Langlands.BaseChange
