import Langlands.Representation.Archimedean.ArchimedeanGLHaarTranspose
import Langlands.Representation.Archimedean.MatrixWhittakerDistributionSymmetry
import Langlands.Representation.Archimedean.UnitaryWhittakerDistributionLaws
import Langlands.Representation.Archimedean.UnitaryWhittakerMultiplicityOneStatement
import Langlands.Representation.Archimedean.UnitaryWhittakerTransposeReduction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory TopologicalSpace Langlands.GeneralLinear Langlands.Whittaker
open scoped ComplexConjugate ContDiff Distributions Manifold Matrix.Norms.Operator

namespace Langlands.Archimedean

universe u

private theorem unitaryWhittakerMultiplicityOneOver (F : Type) [RCLike F] :
    UnitaryWhittakerMultiplicityOneOver.{u} F := by
  intro n E _ _ _ π hπ hπu hirr _ ψ ℓ₀ ℓ₁ hW₀ hW₁ hne
  let M := Matrix (Fin (n + 1)) (Fin (n + 1)) F
  let G := Langlands.GeneralLinear (n + 1) F
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : LocallyCompactSpace G := (Units.isOpenEmbedding_val (R := M)).locallyCompactSpace
  let : SecondCountableTopology G :=
    (Units.isOpenEmbedding_val (R := M)).isEmbedding.secondCountableTopology
  let μ : Measure G := Measure.haar
  let : μ.IsHaarMeasure := by dsimp [μ]; infer_instance
  let e := weylTransposeHomeomorph n F
  let θ := (weylTransposeInvMulEquiv F n).toMulEquiv
  have hθ (x : G) : (e x)⁻¹ = θ x := rfl
  obtain ⟨hRight, hInv, -, hμθ⟩ := archimedeanGLHaar_symmetries F n μ
  let : μ.IsMulRightInvariant := hRight
  let : μ.IsInvInvariant := hInv
  have he := contMDiff_weylTransposeHomeomorph F n
  have he' := contMDiff_weylTransposeHomeomorph_symm F n
  obtain ⟨c, hc⟩ := exists_matrixSmoothTraceCasimir_eq_smul π μ hπ hπu hirr
  let restrictTest := matrixTestFunctionKernelEquiv (F := F) (n := n + 1)
  have hsym (ℓ : smoothVectors (matrixModel F (n + 1)) π →ₗ[ℂ] ℂ)
      (hW : IsWhittakerFunctional (matrixModel F (n + 1)) π
        (upperUnipotent (n + 1) F) (standardCharacter ψ n) ℓ)
      (f : smoothCompactKernels M G) :
      unitaryWhittakerCoefficient μ π hπ hπu ℓ ℓ₀ hW₀.1 (gardingKernelPullback e he f) =
        unitaryWhittakerCoefficient μ π hπ hπu ℓ ℓ₀ hW₀.1 f := by
    let g := restrictTest.symm f
    have hg : restrictTest g = f := restrictTest.apply_symm_apply f
    have hp : restrictTest (matrixWeylTransposeTest F n g) = gardingKernelPullback e he f := by
      apply Subtype.ext
      funext x
      change g (matrixWeylTranspose F n x.val) = f.val (e x)
      rw [matrixWeylTranspose_val]
      exact congrArg (fun k : smoothCompactKernels M G => k.val (e x)) hg
    have h := matrixDistribution_weylTranspose_invariant F n (ψ.scale (-1))
      (unitaryWhittakerDistribution μ π hπ hπu ℓ₀ hW₀.1 ℓ hW.1) (conj c)
      (unitaryWhittakerDistribution_Casimir μ π hπ hπu ℓ ℓ₀ hW.1 hW₀.1 c hc)
      (unitaryWhittakerDistribution_covariance (μ := μ) hπ hπu ψ hW hW₀) g
    change unitaryWhittakerCoefficient μ π hπ hπu ℓ ℓ₀ hW₀.1
        (restrictTest (matrixWeylTransposeTest F n g)) =
      unitaryWhittakerCoefficient μ π hπ hπu ℓ ℓ₀ hW₀.1 (restrictTest g) at h
    rw [hp, hg] at h
    exact h
  exact proportional_of_unitaryWhittakerCoefficient_transpose e he he' θ hθ μ hμθ
    π hπ hπu hirr ℓ₀ ℓ₁ hW₀.1 hW₁.1 hne (hsym ℓ₀ hW₀) (hsym ℓ₁ hW₁)

/-- Continuous Whittaker multiplicity one on the smooth vectors of a unitary
archimedean general linear representation, in the exact Library formulation. -/
theorem unitaryWhittakerMultiplicityOne : UnitaryWhittakerMultiplicityOneStatement.{u} :=
  ⟨unitaryWhittakerMultiplicityOneOver ℝ, unitaryWhittakerMultiplicityOneOver ℂ⟩

end Langlands.Archimedean
