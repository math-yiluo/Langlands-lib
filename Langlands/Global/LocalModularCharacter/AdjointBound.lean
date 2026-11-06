import Langlands.Global.LocalModularCharacter.IdentityChart
import Langlands.Global.LocalModularCharacter.ChartEstimates
import Langlands.Global.LocalModularCharacter.HaarScaleNorm
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # The modular character of `G(K)` is bounded by the Haar scaling of `Ad`

Let `G` be a smooth affine group scheme of finite type over a field `F`, and `K` a complete,
proper, nontrivially normed field that is an `F`-algebra, either ultrametric or a
finite-dimensional real normed space. The modular character of `G(K)` at `g` is at most the
factor by which a linear automorphism of `K^d` with the determinant of `Ad(g)` scales additive
Haar measure. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Langlands.GroupScheme
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Global.LocalModularCharacter

attribute [local instance] identityChartTopology identityChartTopologicalRing
  identityChartPointsTopology identityChartPointsTopologicalGroup
  chartLieKernelCommGroup chartLieKernelModule

variable {F : Type u} [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K] [ProperSpace K]
  [LocallyCompactSpace (G.affinePoints (CommAlgCat.of F K))]
  [T2Space (G.affinePoints (CommAlgCat.of F K))]
  [SecondCountableTopology (G.affinePoints (CommAlgCat.of F K))]
  [MeasurableSpace (G.affinePoints (CommAlgCat.of F K))]
  [BorelSpace (G.affinePoints (CommAlgCat.of F K))]

/-- **Ultrametric bound.** Over an ultrametric field, the modular character of `G(K)` at `g` is
at most any common value `c` of the Haar scaling factors of linear automorphisms of `K^d`
with the determinant of `Ad(g)`. -/
theorem modularCharacter_le_of_adjoint_ultrametric [IsUltrametricDist K] (hG : Smooth G.X.hom)
    (g : G.affinePoints (CommAlgCat.of F K)) (c : ℝ≥0)
    (hc : ∀ (d : ℕ) [MeasurableSpace (Fin d → K)] [BorelSpace (Fin d → K)]
      (A : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      LinearMap.det (A : (Fin d → K) →ₗ[K] (Fin d → K)) = LinearMap.det (adjoint G K g) →
        addEquivAddHaarChar (linearPiContinuousAddEquiv A) = c) :
    Measure.modularCharacter g ≤ c := by
  obtain ⟨d, φ, h1, h0, ⟨L, hT, hL⟩, hconj⟩ := exists_identityChart G hG (K := K)
  obtain ⟨A, hA, hdet⟩ := hconj g
  let : MeasurableSpace (Fin d → K) := borel _
  have : BorelSpace (Fin d → K) := ⟨rfl⟩
  rw [← hc d A.toLinearEquiv hdet]
  exact modularCharacter_le_of_chart_ultrametric φ h1 h0 hT hL g A hA.hasFDerivAt _
    fun _ => rfl

/-- **Archimedean bound.** Over a field that is a finite-dimensional real normed space, the
modular character of `G(K)` at `g` is at most any common value `c` of the Haar scaling factors
of linear automorphisms of `K^d` with the determinant of `Ad(g)`. -/
theorem modularCharacter_le_of_adjoint_real [NormedSpace ℝ K] [FiniteDimensional ℝ K]
    (hG : Smooth G.X.hom) (g : G.affinePoints (CommAlgCat.of F K)) (c : ℝ≥0)
    (hc : ∀ (d : ℕ) [MeasurableSpace (Fin d → K)] [BorelSpace (Fin d → K)]
      (A : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      LinearMap.det (A : (Fin d → K) →ₗ[K] (Fin d → K)) = LinearMap.det (adjoint G K g) →
        addEquivAddHaarChar (linearPiContinuousAddEquiv A) = c) :
    Measure.modularCharacter g ≤ c := by
  obtain ⟨d, φ, h1, h0, ⟨L, hT, hL⟩, hconj⟩ := exists_identityChart G hG (K := K)
  obtain ⟨A, hA, hdet⟩ := hconj g
  let : MeasurableSpace (Fin d → K) := borel _
  have : BorelSpace (Fin d → K) := ⟨rfl⟩
  rw [← hc d A.toLinearEquiv hdet]
  exact modularCharacter_le_of_chart_real φ h1 h0 hT hL g A hA.hasFDerivAt _ fun _ => rfl

end Langlands.Global.LocalModularCharacter
