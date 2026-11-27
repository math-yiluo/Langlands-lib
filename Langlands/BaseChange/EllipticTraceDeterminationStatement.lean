import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.EllipticSupport
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Character.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Elliptic determination of traces at elliptic test functions

For a nonarchimedean local field `F` of characteristic zero and `0 < n`: if a finite linear
combination of the characters of irreducible admissible representations of `GL_n(F)` vanishes on
every test function supported in the regular elliptic set, then it vanishes at every test
function whose orbital integrals vanish at the regular semisimple elements that are not
elliptic. This is the consequence of Harish-Chandra's local integrability theorem (Harish-Chandra
1999, Theorem 16.3) and of the Weyl integration formula (Henniart–Lemaire 2011, II.2.10 (2)) used
in the proof of Arthur–Clozel 1989, Chapter 1, Lemma 2.12. This file states the proposition and
does not prove it. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis JacquetLanglands
open scoped BigOperators

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- **Elliptic determination of traces.** For a nonarchimedean local field `F` of characteristic
zero, `0 < n` and a Haar measure `μ` on `GL_n(F)` (Borel σ-algebra): let `ρ i` (`i` in a finite
type `I`) be irreducible admissible representations of `GL_n(F)` on `V i : Type uV` and
`a : I → ℂ`. If `∑ i, a i * tr (ρ i)(f) = 0` for every Schwartz–Bruhat `f` supported in the
regular elliptic set, then `∑ i, a i * tr (ρ i)(f) = 0` for every Schwartz–Bruhat `f` whose
orbital integrals (for `μ`) vanish at every regular semisimple element that is not regular
elliptic. -/
def EllipticTraceDeterminationStatement.{u, uI, uV} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
      (I : Type uI) [Fintype I] (V : I → Type uV) [∀ i, AddCommGroup (V i)]
      [∀ i, Module ℂ (V i)] (ρ : (i : I) → Representation ℂ (GeneralLinear n F) (V i))
      (hρ : ∀ i, IsAdmissible (ρ i)), (∀ i, (ρ i).IsIrreducible) →
      ∀ a : I → ℂ,
        (∀ f : SchwartzBruhat (GeneralLinear n F), IsEllipticSupported f →
          ∑ i, a i * Character.distribution μ (ρ i) (hρ i) f = 0) →
        ∀ f : SchwartzBruhat (GeneralLinear n F),
          OrbitalIntegralsVanishOffElliptic μ (f : GeneralLinear n F → ℂ) →
          ∑ i, a i * Character.distribution μ (ρ i) (hρ i) f = 0

end Langlands.BaseChange
