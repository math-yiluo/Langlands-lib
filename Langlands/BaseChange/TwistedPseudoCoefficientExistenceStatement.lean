import Langlands.BaseChange.PseudoCoefficient

/-!
# Existence of twisted pseudo-coefficients of σ-discrete series representations

Henniart–Lemaire (2011), II.5.13, Proposition (printed p. 113), and Arthur–Clozel (1989),
Chapter 1, Corollary 2.10 (printed p. 18), for a cyclic field extension `E` of a
nonarchimedean local field `F` of characteristic zero. Stated as a proposition, not proved
here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

/-- Existence of twisted pseudo-coefficients (Henniart–Lemaire 2011, II.5.13, Proposition;
Arthur–Clozel 1989, Chapter 1, Corollary 2.10). Let `F` be a nonarchimedean local field of
characteristic zero, `E` a field that is a cyclic `F`-algebra of group `⟨σ⟩` of order `l`
(with its module topology), and give `GL_n(E)` its Borel σ-algebra. For every σ-discrete
series representation `τ` of `GL_n(E)` on a complex vector space `W`, every character `χ`
of the centre that is the central character of `τ`, every isomorphism `A` of `τ` onto
`τ^σ`, and every Haar measure `μ` on `GL_n(E)`, there is `φ ∈ C^∞_c(GL_n(E))` that is a
twisted pseudo-coefficient of `(τ, A)` with central character `χ`. -/
def TwistedPseudoCoefficientExistenceStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      IsSigmaDiscreteSeries σ n τ →
      ∀ χ : Subgroup.center (GeneralLinear n E) →* ℂˣ, HasCentralCharacterRep τ χ →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        ∃ φ : SchwartzBruhat (GeneralLinear n E),
          IsTwistedPseudoCoefficient μ (entrywiseAut σ n) χ τ hτ A φ

end Langlands.BaseChange
