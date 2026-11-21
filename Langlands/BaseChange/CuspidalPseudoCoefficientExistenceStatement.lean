import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Group.GL.LocalFieldTopology
import Langlands.JacquetLanglands.EssentiallySquareIntegrable

/-!
# Existence of elliptic pseudo-coefficients for the discrete series of `GL_n(F)`

For a nonarchimedean local field `F` of characteristic zero, `0 < n`, and an irreducible
admissible square-integrable representation `π` of `GL_n(F)` with central character `χ`, there
is a pseudo-coefficient `f` of `π` that kills the characters of admissible representations
parabolically induced from irreducible admissible representations of proper standard Levi
subgroups. The orbital integrals of `f` vanish at regular semisimple elements that are not
regular elliptic and are nonzero at regular elliptic elements of a neighbourhood of `1`.
See Kazhdan (1986), Theorems J(b) and K, and Henniart–Lemaire (2011), II.5.14,
Proposition 2, and II.6.7. The paired Markdown explains the sources and the existential form.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.JacquetLanglands

universe u uV

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- Existence of elliptic pseudo-coefficients (Kazhdan 1986, Theorems J (b) and K;
Henniart–Lemaire II.5.14 and II.6.7, for `E = F` and `σ = 1`). Let `F` be a nonarchimedean
local field of characteristic zero and `0 < n`, with `GL_n(F)` carrying its Borel σ-algebra.
Let `π` be an irreducible admissible square-integrable representation of `GL_n(F)` on a
complex vector space `V`, with central character `χ`, and let `μ` be a Haar measure on
`GL_n(F)`. Then there is `f ∈ C^∞_c(GL_n(F))` such that

* (a) `f` is a pseudo-coefficient of `π` with central character `χ`;
* (b) for every standard block shape `B` with at least two blocks and every irreducible
  admissible representation `Ξ` of the Levi product of `B` (carrier in the universe of `V`),
  if the unnormalized smooth induction of `Ξ` from the standard upper block parabolic
  subgroup is admissible, its character vanishes at `f`;
* (c) the orbital integrals of `f` vanish at every regular semisimple element that is not
  regular elliptic;
* (d) there is a neighbourhood `U` of `1` such that, at every regular elliptic `γ ∈ U`, the
  orbital integral of `f` is nonzero for every right Haar measure on the centralizer of `γ`
  and every compatible quotient measure. -/
def CuspidalPseudoCoefficientExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ),
    0 < n →
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GeneralLinear n F) V)
      (hπ : IsAdmissible π), π.IsIrreducible → IsSquareIntegrable π →
      ∀ χ : Subgroup.center (GeneralLinear n F) →* ℂˣ, HasCentralCharacterRep π χ →
      ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
      ∃ f : SchwartzBruhat (GeneralLinear n F),
        -- (a) `f` is a pseudo-coefficient of `π`
        IsPseudoCoefficient μ χ π hπ f ∧
        -- (b) the characters of properly induced representations vanish at `f`
        (∀ B : BlockShape n, 2 ≤ B.length →
          ∀ (X : Type uV) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi F) X),
            IsAdmissible Ξ → Ξ.IsIrreducible →
            ∀ h : IsAdmissible
                (Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))),
              Character.distribution μ
                (Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))) h f =
                0) ∧
        -- (c) the orbital integrals of `f` vanish off the elliptic set
        OrbitalIntegralsVanishOffElliptic μ ⇑f ∧
        -- (d) nonvanishing at the regular elliptic elements near `1`
        ∃ U ∈ nhds (1 : GeneralLinear n F), ∀ γ ∈ U, IsRegularElliptic γ →
          ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
            (νγ : Measure (LeftQuotient (glCentralizer γ))),
            IsCompatible (glCentralizer γ) μ μγ νγ → orbitalIntegral γ νγ ⇑f ≠ 0

end Langlands.BaseChange
