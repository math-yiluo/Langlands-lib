import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing

/-!
# Homogeneity of nilpotent orbital integrals

Harish-Chandra's Lemma 3.2 for the Lie algebra `A` of the unit group of a finite-dimensional
semisimple algebra over a nonarchimedean local field `F` of characteristic zero: the orbital
distribution `μ_N` of a nilpotent element `N` satisfies `μ_N(f_{t²}) = |t|^{d} μ_N(f)` for
`t ∈ Fˣ`, where `f_s(X) = f(s⁻¹ X)` (`scalarDilation`), `|t| = distribHaarChar F t` is the
modulus of `F` and `d = dim_F A - dim_F C_A(N)` is the dimension of the orbit of `N`
(`LieAlgebraNilpotentOrbitalHomogeneityStatement`). The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §3.1, printed pp. 17–19, Lemma 3.2 (Lemma 3): "Fix `O ∈ O(0)`. Then
`ρ(t²) μ_O = |t|^{d(O)} μ_O`", where `(ρ(t)T)(f) = T(f_t)`, `f_t(X) = f(t⁻¹X)` and `d(O)` is the
dimension of `O`. Kottwitz, *Harmonic analysis on reductive p-adic groups and Lie algebras*
(Clay Math. Proc. 4, 2005), Lemma 17.2, printed p. 461, states the same identity as
`μ_O(f_{α²}) = |α|^{-dim O} μ_O(f)` for `f_β(X) = f(βX)`.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Lemma 3.2.** For every nonarchimedean local field `F` of characteristic
zero, every finite-dimensional semisimple `F`-algebra `A` with its module topology (and a Borel
σ-algebra on `Aˣ`), every nilpotent `N : A`, every Haar measure `μG` on `Aˣ`, every
right-invariant Haar measure `μH` on the centralizer `C` of `N`, every compatible quotient
measure `ν` on `C \ Aˣ` with absolutely convergent orbital integrals, every `t ∈ Fˣ` and every
Schwartz–Bruhat function `f`:
`μ_N(f_{t²}) = |t|^d μ_N(f)`, with `f_{t²}(X) = f(t⁻² X)`, `|t| = distribHaarChar F t` the
modulus of `F` and `d = dim_F A - dim_F C_A(N)`, `C_A(N)` the centralizer of `N` in `A`. -/
def LieAlgebraNilpotentOrbitalHomogeneityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ N : A, IsNilpotent N →
      ∀ [MeasurableSpace (LeftQuotient (conjugationCentralizer N))]
        [BorelSpace (LeftQuotient (conjugationCentralizer N))]
        (μG : Measure Aˣ) [μG.IsHaarMeasure]
        (μH : Measure (conjugationCentralizer N)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
        (ν : Measure (LeftQuotient (conjugationCentralizer N))),
        IsCompatible (conjugationCentralizer N) μG μH ν →
        ∀ (hconv : OrbitalIntegralConverges N ν) (t : Fˣ) (f : SchwartzBruhat A),
          orbitalDistribution N ν hconv (scalarDilation (t ^ 2) f) =
            ((distribHaarChar F t : ℝ) : ℂ) ^
                (Module.finrank F A - Module.finrank F (Subalgebra.centralizer F {N})) *
              orbitalDistribution N ν hconv f

end Langlands.HarmonicAnalysis
