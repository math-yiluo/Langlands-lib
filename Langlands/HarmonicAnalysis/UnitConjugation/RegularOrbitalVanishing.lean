import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityStatement
import Langlands.Representation.Hecke.TestFunction
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Harish-Chandra's space `D₀`, nilpotent orbital distributions and dilations

Let `A` be a finite-dimensional algebra over a nonarchimedean local field `F`, the Lie algebra
of its unit group `Aˣ`. This module names the objects of Harish-Chandra's proof of Theorem 3.1
(`LieAlgebraRegularOrbitalDensityStatement`):

* `RegularOrbitalVanishing F A f`: all orbital integrals of `f` over regular orbits vanish, for
  every compatible quotient measure with absolutely convergent orbital integrals; this is
  membership of `f` in Harish-Chandra's space `D₀` (the hypothesis of
  `LieAlgebraRegularOrbitalDensityStatement`);
* `RegularOrbitalDensityFor F A`: Theorem 3.1 for the single algebra `A`, so that
  `LieAlgebraRegularOrbitalDensityStatement` is `RegularOrbitalDensityFor F A` for all `F` and
  `A` (`lieAlgebraRegularOrbitalDensityStatement_iff`);
* `nilpotentOrbitals A`: the orbital distributions `μ_O` of nilpotent elements, for all
  compatible quotient measures with convergent orbital integrals;
* `scalarDilation s f`: the test function `X ↦ f(s⁻¹ X)` for `s ∈ Fˣ`, Harish-Chandra's `f_s`.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §3, printed p. 17: "Let `D₀` be the space of all `f ∈ D` such that
`φ_f^h = 0` for all Cartan subalgebras `h` of `g`"; §3.1, printed p. 17: "For `f ∈ D`,
`X ∈ g`, and `t ∈ Ω^×` define `f_t(X) = f(t⁻¹X)`", and the orbital integral `μ_O` of an orbit
`O`. The identification of `D₀` with the vanishing of all regular orbital integrals is explained
in the Markdown page of `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityStatement`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.UnitConjugation

open QuotientIntegration

universe u v

section Vanishing

variable (F : Type u) [Field F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A]
  [TopologicalSpace A] [IsTopologicalRing A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]

/-- Harish-Chandra's condition `f ∈ D₀`: the orbital integral `∫_{C \ Aˣ} f(g⁻¹ X g) dν` of `f`
vanishes for every regular `X ∈ regularSet F A`, every Borel σ-algebra on the coset space of the
centralizer `C` of `X`, every Haar measure `μG` on `Aˣ`, every right-invariant Haar measure `μH`
on `C`, every compatible quotient measure `ν` and every proof of absolute convergence. -/
def RegularOrbitalVanishing (f : SchwartzBruhat A) : Prop :=
  ∀ X ∈ regularSet F A,
    ∀ [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
      [BorelSpace (LeftQuotient (conjugationCentralizer X))]
      (μG : Measure Aˣ) [μG.IsHaarMeasure]
      (μH : Measure (conjugationCentralizer X)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
      (ν : Measure (LeftQuotient (conjugationCentralizer X))),
      IsCompatible (conjugationCentralizer X) μG μH ν →
      ∀ hconv : OrbitalIntegralConverges X ν, orbitalDistribution X ν hconv f = 0

/-- The orbital distributions of the nilpotent elements of `A`: the distributions
`f ↦ ∫_{C \ Aˣ} f(g⁻¹ N g) dν` for nilpotent `N`, every Borel σ-algebra on the coset space of the
centralizer `C` of `N`, every Haar measure `μG` on `Aˣ`, every right-invariant Haar measure `μH`
on `C`, every compatible quotient measure `ν` and every proof of absolute convergence. -/
def nilpotentOrbitals : Set (Distribution A) :=
  {R | ∃ N : A, IsNilpotent N ∧
    ∃ (_ : MeasurableSpace (LeftQuotient (conjugationCentralizer N)))
      (_ : BorelSpace (LeftQuotient (conjugationCentralizer N)))
      (μG : Measure Aˣ) (_ : μG.IsHaarMeasure)
      (μH : Measure (conjugationCentralizer N)) (_ : μH.IsHaarMeasure)
      (_ : μH.IsMulRightInvariant)
      (ν : Measure (LeftQuotient (conjugationCentralizer N)))
      (_ : IsCompatible (conjugationCentralizer N) μG μH ν)
      (hconv : OrbitalIntegralConverges N ν), R = orbitalDistribution N ν hconv}

end Vanishing

section Dilation

variable {F : Type u} [Field F] {A : Type v} [AddCommGroup A] [Module F A]
  [TopologicalSpace A] [ContinuousConstSMul F A]

/-- Harish-Chandra's dilation `f_s(X) = f(s⁻¹ X)` of a test function by `s ∈ Fˣ`. -/
def scalarDilation (s : Fˣ) : SchwartzBruhat A ≃ₗ[ℂ] SchwartzBruhat A :=
  Hecke.TestFunction.pullback (Homeomorph.smul s⁻¹)

@[simp]
theorem scalarDilation_apply (s : Fˣ) (f : SchwartzBruhat A) (X : A) :
    scalarDilation s f X = f (s⁻¹ • X) := rfl

end Dilation

section Density

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- Harish-Chandra's Theorem 3.1 for the single algebra `A`: for every module topology on `A`
and Borel σ-algebra on `Aˣ`, every conjugation-invariant distribution annihilates every test
function in `D₀`. -/
def RegularOrbitalDensityFor : Prop :=
  ∀ [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ f : SchwartzBruhat A, RegularOrbitalVanishing F A f →
      ∀ T : Distribution A, IsConjugationInvariant T → T f = 0

end Density

/-- `LieAlgebraRegularOrbitalDensityStatement` is Theorem 3.1 for every nonarchimedean local
field of characteristic zero and every finite-dimensional semisimple algebra over it. -/
theorem lieAlgebraRegularOrbitalDensityStatement_iff :
    LieAlgebraRegularOrbitalDensityStatement.{u, v} ↔
      ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F] [CharZero F] (A : Type v) [Ring A] [Algebra F A]
        [FiniteDimensional F A] [IsSemisimpleRing A], RegularOrbitalDensityFor F A :=
  Iff.rfl

end Langlands.HarmonicAnalysis.UnitConjugation
