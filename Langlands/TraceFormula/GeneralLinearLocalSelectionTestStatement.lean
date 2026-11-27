import Langlands.TraceFormula.GeneralLinearDiscreteSeriesGlobalizationStatement
import Langlands.BaseChange.CuspForm
import Langlands.BaseChange.OrbitalIntegral
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Character.Basic
import Langlands.Group.GL.LocalFieldTopology

/-!
# Local selection tests at a finite place for the globalization of `GL_n`

Two propositions, stated without proof, about compactly supported smooth test functions on
`GL_{r+1}(K_v)` for a finite place `v` of a number field `K`. They are the local inputs of the
trace-formula globalization of square-integrable representations. Each asks for one test
function `φ` with two properties.

* Selection: the trace of `φ` vanishes on the irreducible admissible representations outside
  a prescribed class, of every central character.
* Orbital nonvanishing: there is a nonempty open set of `GL_{r+1}(K_v)` on which every orbital
  integral of `φ` is nonzero.

In `GeneralLinearDiscreteSeriesSelectionTestStatement` the class is the unitary unramified
determinant twists of a given square-integrable `ρ`, tested on generic unitarizable
representations. In `GeneralLinearSupercuspidalSelectionTestStatement` the class is the
supercuspidal representations, tested on all irreducible admissible representations, and `φ`
also has vanishing constant terms.

`K_v` carries its completion topology, with the valuative relation and the nonarchimedean
local-field structure of `Langlands.Global.CompletionPadic.topologicalData v`, as in
`GeneralLinearDiscreteSeriesGlobalizationStatement`.

Sources: Henniart–Lemaire 2011, II.5.13–II.5.14 and II.6.7–II.6.9 (printed pp. 113–117 and
123–125); Arthur–Clozel 1989, Chapter 1, Lemma 6.5 and its proof (printed pp. 54–55).
See `GeneralLinearLocalSelectionTestStatement.md`.
-/

noncomputable section

set_option autoImplicit false

universe u uV uW

namespace Langlands.TraceFormula

open MeasureTheory HarmonicAnalysis Langlands.Global Langlands.QuotientIntegration Langlands.BaseChange

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- **Selection test for a square-integrable representation.** Let `v` be a finite place of a
number field `K` and `r : ℕ`. Give `K_v` its completion topology and the local-field structure
of `CompletionPadic.topologicalData v`, and `GL_{r+1}(K_v)` its Borel σ-algebra. For every
admissible irreducible representation `ρ` of `GL_{r+1}(K_v)` that is square-integrable modulo
the centre there is `φ ∈ C^∞_c(GL_{r+1}(K_v))` such that:

1. for every irreducible admissible unitarizable representation `π` (carrier in `Type uW`) that
   is generic for some unitary additive character `ψ` of `K_v`, and every Haar measure `μ`, if
   the character of `π` does not vanish at `φ`, then `π` is equivalent to `ρ ⊗ (χ ∘ det)` for a
   character `χ` of `K_vˣ` that is trivial on the units of the completed valuation ring
   (`Valued.v t = 1`) and has absolute value one;
2. there is a nonempty open set `U ⊆ GL_{r+1}(K_v)` such that at every `γ ∈ U` the orbital
   integral of `φ` is nonzero, for every Haar measure on `GL_{r+1}(K_v)`, every right Haar
   measure on the centralizer of `γ` and every compatible quotient measure. -/
def GeneralLinearDiscreteSeriesSelectionTestStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (v : FinitePlace K) (r : ℕ),
    letI : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
    haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).localField
    letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := borel _
    haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1)
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1)
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace (v.adicCompletion K) (r + 1)
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion K)) V),
      IsAdmissible ρ → ρ.IsIrreducible → JacquetLanglands.IsSquareIntegrable ρ →
      ∃ φ : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion K)),
        (∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
          (π : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion K)) W)
          (hπ : IsAdmissible π), π.IsIrreducible → IsUnitarizable π →
          (∃ ψ : UnitaryAdditiveCharacter (v.adicCompletion K),
            Whittaker.IsGeneric ψ r π) →
          ∀ (μ : Measure (GeneralLinear (r + 1) (v.adicCompletion K))) [μ.IsHaarMeasure],
            Character.distribution μ π hπ φ ≠ 0 →
            ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
              (∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → χ t = 1) ∧
              (∀ t : (v.adicCompletion K)ˣ, ‖(χ t : ℂ)‖ = 1) ∧
              Nonempty ((twist (χ.comp GeneralLinear.determinant) ρ).Equiv π)) ∧
        ∃ U : Set (GeneralLinear (r + 1) (v.adicCompletion K)), IsOpen U ∧ U.Nonempty ∧
          ∀ γ ∈ U, ∀ (μ : Measure (GeneralLinear (r + 1) (v.adicCompletion K)))
            [μ.IsHaarMeasure] (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure]
            [μγ.IsMulRightInvariant] (νγ : Measure (LeftQuotient (glCentralizer γ))),
            IsCompatible (glCentralizer γ) μ μγ νγ → orbitalIntegral γ νγ ⇑φ ≠ 0

/-- **Supercuspidal selection test.** Let `v` be a finite place of a number field `K` and
`r : ℕ`, with `K_v` and `GL_{r+1}(K_v)` as in
`GeneralLinearDiscreteSeriesSelectionTestStatement`. There is `φ ∈ C^∞_c(GL_{r+1}(K_v))` such
that:

1. `φ` has vanishing constant terms along the unipotent radicals of all proper standard block
   parabolic subgroups, after any left and right translation;
2. every irreducible admissible representation `π` (carrier in `Type uW`) whose character does
   not vanish at `φ`, for some Haar measure, is supercuspidal;
3. there is a nonempty open set `U ⊆ GL_{r+1}(K_v)` such that at every `γ ∈ U` the orbital
   integral of `φ` is nonzero, for every Haar measure on `GL_{r+1}(K_v)`, every right Haar
   measure on the centralizer of `γ` and every compatible quotient measure. -/
def GeneralLinearSupercuspidalSelectionTestStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (v : FinitePlace K) (r : ℕ),
    letI : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
    haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).localField
    letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := borel _
    haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1)
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1)
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace (v.adicCompletion K) (r + 1)
    ∃ φ : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion K)),
      HasVanishingConstantTerms (⇑φ) ∧
      (∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion K)) W)
        (hπ : IsAdmissible π), π.IsIrreducible →
        ∀ (μ : Measure (GeneralLinear (r + 1) (v.adicCompletion K))) [μ.IsHaarMeasure],
          Character.distribution μ π hπ φ ≠ 0 → GeneralLinear.IsSupercuspidal π) ∧
      ∃ U : Set (GeneralLinear (r + 1) (v.adicCompletion K)), IsOpen U ∧ U.Nonempty ∧
        ∀ γ ∈ U, ∀ (μ : Measure (GeneralLinear (r + 1) (v.adicCompletion K)))
          [μ.IsHaarMeasure] (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure]
          [μγ.IsMulRightInvariant] (νγ : Measure (LeftQuotient (glCentralizer γ))),
          IsCompatible (glCentralizer γ) μ μγ νγ → orbitalIntegral γ νγ ⇑φ ≠ 0

end Langlands.TraceFormula
