import Langlands.BaseChange.EllipticSupport
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Irreducible

/-!
# Rigidity of characters on the regular elliptic set

The statement that, for a nonarchimedean local field `F` of characteristic zero and an open
subgroup `H` of finite index in `Fˣ`, if the character of an irreducible admissible
representation `π` of `GL_n(F)` is a nonzero multiple of the character of an irreducible
supercuspidal representation `π₀` on all test functions supported in the regular elliptic set
with determinants in `H`, then `π` is the twist of `π₀` by `χ ∘ det` for a character `χ` of `Fˣ`
trivial on `H`. It is a formulation, comparing two ordinary characters, of the local
identification step of cyclic base change by the simple trace formula, where
`H = N_{E/F}Eˣ` and the sources compare an ordinary with a twisted trace (Arthur–Clozel 1989,
Chapter 1, §6.3, printed pp. 56–57; Henniart–Lemaire 2011, II.4.6 Théorème (2), II.4.8 and
II.6.13, printed pp. 88, 90–91 and 129–130). This file states the proposition and does not
prove it. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero and `n : ℕ`: let `H` be an open
subgroup of finite index of `Fˣ`, `π` an irreducible admissible representation of `GL_n(F)` on
`V : Type uV`, `π₀` an irreducible supercuspidal representation of `GL_n(F)` on `W : Type uW`,
`c ≠ 0` and `μ` a Haar measure on `GL_n(F)` (Borel σ-algebra). If `tr π(f) = c · tr π₀(f)` for
every Schwartz–Bruhat function `f` supported in the regular elliptic set with `det g ∈ H` whenever
`f g ≠ 0`, then `π ≅ π₀ ⊗ (χ ∘ det)` for some character `χ : Fˣ →* ℂˣ` trivial on `H`. -/
def EllipticTraceRigidityStatement.{u, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ),
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ (H : Subgroup Fˣ), IsOpen (H : Set Fˣ) → H.FiniteIndex →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (π₀ : Representation ℂ (GeneralLinear n F) W) (hπ₀ : GeneralLinear.IsSupercuspidal π₀),
      π.IsIrreducible → π₀.IsIrreducible →
      ∀ (c : ℂ), c ≠ 0 → ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
        (∀ f : SchwartzBruhat (GeneralLinear n F),
          IsEllipticSupported (f : GeneralLinear n F → ℂ) →
          (∀ g : GeneralLinear n F, f g ≠ 0 → GeneralLinear.determinant g ∈ H) →
          Character.distribution μ π hπ f = c * Character.distribution μ π₀ hπ₀.1 f) →
        ∃ χ : Fˣ →* ℂˣ, (∀ h ∈ H, χ h = 1) ∧
          Nonempty (π.Equiv (twist (χ.comp GeneralLinear.determinant) π₀))

end Langlands.BaseChange
