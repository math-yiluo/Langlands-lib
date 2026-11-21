import Langlands.BaseChange.CuspForm
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.OrbitalIntegral
import Langlands.Representation.Classification.Supercuspidal
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Supercuspidal cusp-form pseudo-coefficients with nonzero elliptic orbital integrals

For an irreducible supercuspidal representation `π` of `GL_n(F)` with central character `χ`
(`F` a nonarchimedean local field of characteristic zero), there is a test function `f` that
has vanishing constant terms, is a pseudo-coefficient of `π`, kills the trace of every other
irreducible admissible representation with central character `χ`, and has nonzero orbital
integrals at the regular elliptic elements near `1`.
This module defines an unproved proposition. See the paired Markdown.
-/

namespace Langlands.BaseChange

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u uV

open MeasureTheory HarmonicAnalysis QuotientIntegration TraceFormula JacquetLanglands

/-- **Supercuspidal cusp-form pseudo-coefficients.** For every nonarchimedean local field `F`
of characteristic zero, every `n`, every irreducible supercuspidal representation `π` of
`GL_n(F)` on `V : Type uV` with central character `χ`, and every Haar measure `μ` on
`GL_n(F)`, there is `f ∈ C^∞_c(GL_n(F))` such that
(a) `f` has vanishing constant terms;
(b) `f` is a pseudo-coefficient of `π` for `μ` and `χ`;
(c) the character of every irreducible admissible `π' ≇ π` on `V' : Type uV` with central
character `χ` vanishes at `f`;
(d) there is a neighbourhood `U` of `1` such that the orbital integral of `f` at every regular
elliptic `γ ∈ U` is nonzero, for every right Haar measure on the centralizer of `γ` and every
compatible quotient measure. -/
def SupercuspidalCuspFormStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ),
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π),
      π.IsIrreducible → GeneralLinear.IsSupercuspidal π →
      ∀ χ : Subgroup.center (GeneralLinear n F) →* ℂˣ, HasCentralCharacterRep π χ →
      ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
      ∃ f : SchwartzBruhat (GeneralLinear n F),
        HasVanishingConstantTerms (f : GeneralLinear n F → ℂ) ∧
        IsPseudoCoefficient μ χ π hπ f ∧
        (∀ (V' : Type uV) [AddCommGroup V'] [Module ℂ V']
          (π' : Representation ℂ (GeneralLinear n F) V') (hπ' : IsAdmissible π'),
          π'.IsIrreducible → HasCentralCharacterRep π' χ → IsEmpty (π'.Equiv π) →
          Character.distribution μ π' hπ' f = 0) ∧
        ∃ U ∈ nhds (1 : GeneralLinear n F), ∀ γ ∈ U, IsRegularElliptic γ →
          ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
            (νγ : Measure (LeftQuotient (glCentralizer γ))),
            IsCompatible (glCentralizer γ) μ μγ νγ →
            orbitalIntegral γ νγ (f : GeneralLinear n F → ℂ) ≠ 0

end Langlands.BaseChange
