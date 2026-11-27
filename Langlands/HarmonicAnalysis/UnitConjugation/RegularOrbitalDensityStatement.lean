import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution
import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Invariant distributions are determined by regular orbital integrals

Harish-Chandra's Theorem 3.1 for the Lie algebra `A` of the unit group `Aˣ` of a
finite-dimensional semisimple algebra over a nonarchimedean local field `F` of characteristic
zero: a Schwartz–Bruhat function whose orbital integrals over all regular orbits vanish is
annihilated by every conjugation-invariant distribution on `A`
(`LieAlgebraRegularOrbitalDensityStatement`). The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §1, printed p. 5: for a Cartan subalgebra `h` with split component
`A_h` of its Cartan subgroup, `φ_f(H) = |η(H)|^{1/2} ∫_{G/A_h} f(x.H) dx*` for `H ∈ h' = h ∩ g'`;
§3, printed p. 17: "Let `D₀` be the space of all `f ∈ D` such that `φ_f^h = 0` for all Cartan
subalgebras `h` of `g`", Theorem 3.1 (Theorem 10): "We have `T(f) = 0` for `T ∈ J` and
`f ∈ D₀`."
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Theorem 3.1** for the unit group of a finite-dimensional semisimple
algebra. For every nonarchimedean local field `F` of characteristic zero, every
finite-dimensional semisimple `F`-algebra `A` with its module topology (and a Borel σ-algebra on
`Aˣ`) and every Schwartz–Bruhat function `f` on `A`: if the orbital integral
`∫_{C \ Aˣ} f(g⁻¹ X g) dν` vanishes for every regular `X ∈ g'` (`regularSet F A`), every Haar
measure `μG` on `Aˣ`, every bi-invariant Haar measure `μH` on the centralizer `C` of `X` and
every compatible quotient measure `ν` on `C \ Aˣ` with absolutely convergent orbital
integrals, then `T f = 0` for every conjugation-invariant distribution `T` on `A`. -/
def LieAlgebraRegularOrbitalDensityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ f : SchwartzBruhat A,
      (∀ X ∈ regularSet F A,
        ∀ [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
          [BorelSpace (LeftQuotient (conjugationCentralizer X))]
          (μG : Measure Aˣ) [μG.IsHaarMeasure]
          (μH : Measure (conjugationCentralizer X)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
          (ν : Measure (LeftQuotient (conjugationCentralizer X))),
          IsCompatible (conjugationCentralizer X) μG μH ν →
          ∀ hconv : OrbitalIntegralConverges X ν, orbitalDistribution X ν hconv f = 0) →
      ∀ T : Distribution A, IsConjugationInvariant T → T f = 0

end Langlands.HarmonicAnalysis
