import Langlands.Representation.Archimedean.RealCompactWitnessExtension
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.PartialJacquetIntegral
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-! # Polynomial multiplication in the real compact standard model -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open GramFormula OrthogonalFinitePolynomial PrincipalSeriesExtension

private abbrev O (n : ℕ) := Matrix.unitaryGroup (Fin n) ℝ
private abbrev KF (n : ℕ) (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-- Multiplication by a compact polynomial that is left invariant under the
diagonal signs and the inducing block rotations extends to a standard vector. -/
def RealStandardCompactMultiplierStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    ∀ (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ), Continuous φ →
      φ ∈ polynomialFunctions n →
      (∀ (a : Fin n → ℝˣ) k, φ (signDiagonal (fun i => (a i : ℝ)) * k) = φ k) →
      (∀ p d, realInducedBlockAt ds p = some d → ∀ θ k,
        φ (RealCompactWitnessExtension.compactBlockRotation n p θ * k) = φ k) →
      ∀ f : KF n ds, ∃ F : KF n ds, ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
        F.val (Unitary.toUnits k) = φ k * f.val (Unitary.toUnits k)

theorem realStandardCompactMultiplier : RealStandardCompactMultiplierStatement := by
  intro n ds hn φ hφ hφPoly hsign hrotate f
  let ψ : O n → ℂ := fun k => φ k * f.val (Unitary.toUnits k)
  have hf : Continuous f.val := RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions f.2
  have hψ : Continuous ψ := hφ.mul (hf.comp continuous_unitary_toUnits)
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions hφPoly
  obtain ⟨Q, hQ⟩ := exists_mvPolynomial_of_mem_kFiniteVectors hf f.2.2 1
  have hψPoly (k : O n) :
      ψ k = MvPolynomial.eval (fun ij => (k.val ij.1 ij.2 : ℂ)) (P * Q) := by
    simpa only [ψ, map_mul, hP, one_mul] using
      congrArg (φ k * ·) (hQ k)
  have hψFinite : FiniteDimensional ℂ (translateSpan ψ) := by
    rw [funext hψPoly]
    exact TranslateFinite.finiteDimensional_span_eval (P * Q)
  have hψCov (a : Fin n → ℝˣ) (k : O n) :
      ψ (signDiagonal (fun i => (a i : ℝ)) * k) =
        principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) *
          ψ k := by
    dsimp only [ψ]
    rw [hsign, PartialJacquet.signDiagonal_toUnits, f.2.1.1.2]
    ring
  obtain ⟨F, hF, hval⟩ := principalSeriesExtension n ds ψ hψ hψFinite hψCov
  refine ⟨⟨F, RealBlockPosition.mem_realStandardModule_of_unitaryCompact hn hF.1 ?_, hF.2⟩,
    hval⟩
  intro p d hd j hj g hg
  let k : O n := ⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩
  have hk : Unitary.toUnits k = g := Units.ext rfl
  have hmul (θ : ℝ) :
      F (blockRotation n p θ * g) = φ k * f.val (blockRotation n p θ * g) := by
    have hgl : Unitary.toUnits (RealCompactWitnessExtension.compactBlockRotation n p θ * k) =
        blockRotation n p θ * g := by
      rw [map_mul, hk, RealCompactWitnessExtension.compactBlockRotation_toUnits]
    rw [← hgl, hval]
    change φ (RealCompactWitnessExtension.compactBlockRotation n p θ * k) *
      f.val (Unitary.toUnits (RealCompactWitnessExtension.compactBlockRotation n p θ * k)) = _
    rw [hrotate p d hd θ k]
  calc
    blockFourierCoefficient n p j F g = φ k * blockFourierCoefficient n p j f.val g := by
      unfold blockFourierCoefficient
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [hmul, mul_assoc]
    _ = 0 := by rw [f.2.1.2 p d hd j hj g, mul_zero]

end Langlands.Archimedean
