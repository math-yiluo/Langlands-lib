import Langlands.BaseChange.DeterminantWindow
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.RepresentationTheory.Irreducible

/-!
# Schur orthogonality for cut-off supercuspidal coefficients

The statement that, for a finite field extension `E` of a nonarchimedean local field `F`
with its module topology, an irreducible supercuspidal representation `τ` of `GL_n(E)` and a
Haar measure `μ`, there is a nonzero scalar `d` such that every coefficient
`x ↦ λ(τ(x)⁻¹ w)` of the contragredient, cut off by the determinant window normalized over the
scalars `F^×`, acts on `τ` as the rank-one operator `u ↦ d λ(u) w`. This is Schur orthogonality
modulo the centre (Renard IV.3.3), with `d` the inverse of the formal degree for the quotient
measure of `μ` by a Haar measure of `F^×` giving `O_F^×` volume one.
Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F`, a field `E` finite over `F` with its module topology,
and `0 < n`, write `b = determinantWindow F (n * [E : F])` on `GL_n(E)`. Let `τ` be an
irreducible supercuspidal representation of `GL_n(E)` on `W : Type uW` and `μ` a Haar measure
on `GL_n(E)` (Borel σ-algebra). Then there is `d ≠ 0` such that for every `w ∈ W`, every smooth
linear form `λ` and every Schwartz–Bruhat function `φ` with `φ(x) = b(x) λ(τ(x)⁻¹ w)`, the
integrated operator `τ(φ) = ∫ φ(x) τ(x) dμ(x)` is `u ↦ d λ(u) w`. -/
def SupercuspidalWindowSchurOrthogonalityStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [Field E] [Algebra F E] [Module.Finite F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (n : ℕ), 0 < n →
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : GeneralLinear.IsSupercuspidal τ),
      τ.IsIrreducible → ∀ (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
      ∃ d : ℂ, d ≠ 0 ∧
        ∀ (w : W) (ℓ : SmoothDual τ) (φ : SchwartzBruhat (GeneralLinear n E)),
          (∀ x : GeneralLinear n E, φ x =
            determinantWindow F (n * Module.finrank F E) x * (ℓ : Module.Dual ℂ W) (τ x⁻¹ w)) →
          ∀ u : W, Hecke.integratedAction μ τ hτ.1.1 φ u = (d * (ℓ : Module.Dual ℂ W) u) • w

end Langlands.BaseChange
