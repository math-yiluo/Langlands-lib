import Langlands.HarmonicAnalysis.PartialFourierEquiv
import Langlands.Group.GL.BlockUnipotent
import Langlands.Group.GL.RankMaps
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-! Covariance of the action `rectangularRho0`, transported through the chosen
last-column partial Fourier equivalence, under three kinds of elementary matrices. -/

namespace Langlands.HarmonicAnalysis

/-- The action `rectangularRho0` agrees with right translation on `diag(h, 1)`.
On the upper unipotent matrix `[[I_n, v], [0, 1]]` it multiplies the value at
`[x, y]` by `ψ(⟨y, x v⟩)`. On `diag(1, ..., 1, a)` it is the reciprocal of the
`n`-th power of the Haar character of `a` times right translation by the inverse
matrix. This proposition does not supply a proof. -/
def PartialFourierCovarianceStatement.{uK} : Prop :=
  ∀ {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (n : ℕ)
    (hsd : IsSelfDual ψ μ),
    (∀ (h : Langlands.GeneralLinear n K)
        (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)),
      rectangularRho0 ψ μ n hsd (Langlands.GeneralLinear.rankInclusion 1 h) Φ =
        rectangularTranslate (Langlands.GeneralLinear.rankInclusion 1 h) Φ) ∧
    (∀ (v : Fin n → K) (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
        (x : Matrix (Fin n) (Fin n) K) (y : Fin n → K),
      rectangularRho0 ψ μ n hsd
          (Langlands.GeneralLinear.blockUnipotent (a := n) (b := 1) (n := n + 1) rfl
            (fun i _ => v i)) Φ (rectangularJoin x y) =
        Φ (rectangularJoin x y) * ψ.complex (rowPairing y (Matrix.mulVec x v))) ∧
    ∀ (a : Kˣ) (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)),
      rectangularRho0 ψ μ n hsd
          (Langlands.GeneralLinear.blockSum
            ((1 : Langlands.GeneralLinear n K), Langlands.GeneralLinear.scalar (n := 1) a)) Φ =
        ((((MeasureTheory.distribHaarChar K a : ℝ) : ℂ) ^ n)⁻¹) •
          rectangularTranslate
            (Langlands.GeneralLinear.blockSum
              ((1 : Langlands.GeneralLinear n K), Langlands.GeneralLinear.scalar (n := 1) a))⁻¹
            Φ

end Langlands.HarmonicAnalysis
