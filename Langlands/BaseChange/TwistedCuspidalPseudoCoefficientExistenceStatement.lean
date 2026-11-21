import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter

/-!
# Existence of σ-elliptic twisted pseudo-coefficients for the σ-discrete series of `GL_n(E)`

For a nonarchimedean local field `F` of characteristic zero, a cyclic field extension `E` of
`F` of degree `l` with generator `σ`, a σ-discrete series representation `τ` of `GL_n(E)`
with central character `χ`, `0 < n`, and an isomorphism `A` of `τ` onto `τ^σ`, there is a
twisted pseudo-coefficient `φ` of `(τ, A)` that kills the twisted characters of the
irreducible representations parabolically induced from σ-stable irreducible admissible
representations of proper standard Levi subgroups, whose σ-orbital integrals vanish at every
σ-regular element that is not σ-elliptic, and whose σ-orbital integrals do not vanish on some
nonempty open set of σ-elliptic elements (Henniart–Lemaire 2011, II.5.14, Proposition 2 and
Corollaire 2, printed pp. 115-117; Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (ii), printed
p. 19). See the paired Markdown for the sources and the reasons for the existential form.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.JacquetLanglands

universe u v uW

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- Existence of σ-elliptic twisted pseudo-coefficients (Henniart–Lemaire II.5.14,
Proposition 2 and Corollaire 2; Arthur–Clozel, Chapter 1, Lemma 2.12 (ii)). Let `F` be a
nonarchimedean local field of characteristic zero, `E` a field that is a cyclic `F`-algebra
of degree `l` with generator `σ` and carries the module topology, and `0 < n`, with `GL_n(E)`
carrying its Borel σ-algebra. Let `τ` be a σ-discrete series representation of `GL_n(E)` on a
complex vector space `W`, admissible, with central character `χ`, let `A` be an isomorphism of
`τ` onto `τ^σ = τ ∘ entrywiseAut σ n`, and let `μ` be a Haar measure on `GL_n(E)`. Then there
is `φ ∈ C^∞_c(GL_n(E))` such that

* (a) `φ` is a twisted pseudo-coefficient of `(τ, A)` with central character `χ`;
* (b) for every standard block shape `B` with at least two blocks and every irreducible
  admissible σ-stable representation `Ξ` of the Levi product of `B` (carrier in the universe
  of `W`) whose unnormalized smooth induction from the standard upper block parabolic
  subgroup is irreducible and admissible, the twisted character of that induced representation
  with any isomorphism `A'` onto its σ-conjugate vanishes at `φ`;
* (c) the σ-orbital integrals of `φ` vanish at every σ-regular element that is not
  σ-elliptic;
* (d) there is a nonempty open set `V` of σ-elliptic elements of `GL_n(E)` such that, at
  every `δ ∈ V`, the σ-orbital integral of `φ` is nonzero for every right Haar measure on the
  σ-centralizer of `δ` and every compatible quotient measure. -/
def TwistedCuspidalPseudoCoefficientExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l : ℕ) (hE : IsCyclicAlgebra σ l) (n : ℕ),
    0 < n →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GeneralLinear n E) W)
      (hτ : IsAdmissible τ), IsSigmaDiscreteSeries σ n τ →
      ∀ χ : Subgroup.center (GeneralLinear n E) →* ℂˣ, HasCentralCharacterRep τ χ →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
      ∃ φ : SchwartzBruhat (GeneralLinear n E),
        -- (a) `φ` is a twisted pseudo-coefficient of `(τ, A)`
        IsTwistedPseudoCoefficient μ (entrywiseAut σ n) χ τ hτ A φ ∧
        -- (b) the twisted characters of irreducible properly induced representations vanish
        (∀ B : BlockShape n, 2 ≤ B.length →
          ∀ (X : Type uW) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
            IsAdmissible Ξ → Ξ.IsIrreducible → IsLeviSigmaStable σ B Ξ →
            (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))).IsIrreducible →
            ∀ (h : IsAdmissible
                (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))
              (A' : SigmaIntertwiner σ n
                (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))),
              twistedDistribution μ
                (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))) h
                A'.toLinearMap φ = 0) ∧
        -- (c) the σ-orbital integrals of `φ` vanish off the σ-elliptic set
        SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ ∧
        -- (d) nonvanishing on a nonempty open set of σ-elliptic elements
        ∃ V : Set (GeneralLinear n E), IsOpen V ∧ V.Nonempty ∧
          (∀ δ ∈ V, IsSigmaElliptic σ l δ) ∧
          ∀ δ ∈ V,
            ∀ (μδ : Measure (sigmaCentralizer σ n δ)) [μδ.IsHaarMeasure]
              [μδ.IsMulRightInvariant] (νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ))),
              IsCompatible (sigmaCentralizer σ n δ) μ μδ νδ → sigmaOrbitalIntegral σ n δ νδ ⇑φ ≠ 0

end Langlands.BaseChange
