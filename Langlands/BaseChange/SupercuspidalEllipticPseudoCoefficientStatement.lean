import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.RepresentationTheory.Irreducible

/-!
# Elliptic pseudo-coefficients of supercuspidal representations

For a nonarchimedean local field `F` of characteristic zero, `0 < n`, and an irreducible
supercuspidal representation `π` of `GL_n(F)` with central character `χ`, there is a
Schwartz–Bruhat function `f` whose orbital integrals vanish at the regular semisimple elements
that are not elliptic, with `tr π(f) = 1` and `tr ρ(f) = 0` for every irreducible admissible
representation `ρ` with central character `χ` that is not isomorphic to `π`. This is the
untwisted case of Arthur–Clozel 1989, Chapter 1, Corollary 2.10 and Lemma 2.12 (ii), for the
cut-off matrix coefficients of a supercuspidal representation, tested against all irreducible
admissible representations with the given central character. This file states the proposition
and does not prove it. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis JacquetLanglands

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- **Elliptic pseudo-coefficients of supercuspidal representations.** For a nonarchimedean
local field `F` of characteristic zero, `0 < n`, an irreducible supercuspidal representation
`π` of `GL_n(F)` on `V : Type uV` with central character `χ`, and a Haar measure `μ` on
`GL_n(F)` (Borel σ-algebra), there is a Schwartz–Bruhat function `f` such that the orbital
integrals of `f` (for `μ`) vanish at every regular semisimple element that is not regular
elliptic, `tr π(f) = 1`, and `tr ρ(f) = 0` for every irreducible admissible representation `ρ`
of `GL_n(F)` on a space `W : Type uW` with central character `χ` that is not isomorphic to
`π`. -/
def SupercuspidalEllipticPseudoCoefficientStatement.{u, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : GeneralLinear.IsSupercuspidal π),
      π.IsIrreducible →
      ∀ χ : Subgroup.center (GeneralLinear n F) →* ℂˣ, HasCentralCharacterRep π χ →
      ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
      ∃ f : SchwartzBruhat (GeneralLinear n F),
        OrbitalIntegralsVanishOffElliptic μ (f : GeneralLinear n F → ℂ) ∧
        Character.distribution μ π hπ.1 f = 1 ∧
        ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
          (ρ : Representation ℂ (GeneralLinear n F) W) (hρ : IsAdmissible ρ),
          ρ.IsIrreducible → HasCentralCharacterRep ρ χ → IsEmpty (ρ.Equiv π) →
          Character.distribution μ ρ hρ f = 0

end Langlands.BaseChange
