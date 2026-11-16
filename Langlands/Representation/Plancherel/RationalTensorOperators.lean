import Langlands.Representation.Plancherel.CompactIntertwiningComposition
import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Whole-operator rationality for tensor products -/

noncomputable section

open scoped BigOperators TensorProduct NNReal

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe uG uI uV uW uZ uV' uW'

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {Ω Λ : Set (unramifiedCharacters ν)}

/-- A fixed bilinear map sends two finite regular expansions to one. -/
theorem IsPolynomialOn.bilinear {f : Ω → V} {g : Ω → W}
    (hf : IsPolynomialOn Ω f) (hg : IsPolynomialOn Ω g)
    (T : V →ₗ[ℂ] W →ₗ[ℂ] Z) :
    IsPolynomialOn Ω (fun χ => T (f χ) (g χ)) := by
  obtain ⟨n, b, v, hf⟩ := hf
  have hsum := IsPolynomialOn.sum (Finset.univ : Finset (Fin n))
    (f := fun i χ => (b i).val χ.val • T (v i) (g χ))
    (fun i _ => (hg.linearMap (T (v i))).regular_smul (b i))
  convert hsum using 1
  funext χ
  rw [hf χ, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Tensoring polynomial operators preserves the fixed-vector notion of
polynomiality, without a finite-dimensionality hypothesis. -/
theorem IsPolynomialOperatorOn.tensor
    {A : Ω → V →ₗ[ℂ] V'} {B : Ω → W →ₗ[ℂ] W'}
    (hA : IsPolynomialOperatorOn Ω A) (hB : IsPolynomialOperatorOn Ω B) :
    IsPolynomialOperatorOn Ω (fun χ => TensorProduct.map (A χ) (B χ)) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
      exact (hA v).bilinear (hB w) (TensorProduct.mk ℂ V' W')
  | add t s ht hs =>
      simpa only [map_add] using ht.add hs

/-- The product of two whole-operator denominators clears their tensor,
before any input tensor is chosen. -/
theorem IsRationalOperatorOn.tensor
    {A : Ω → V →ₗ[ℂ] V'} {B : Ω → W →ₗ[ℂ] W'}
    (hA : IsRationalOperatorOn Ω A) (hB : IsRationalOperatorOn Ω B) :
    IsRationalOperatorOn Ω (fun χ => TensorProduct.map (A χ) (B χ)) := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨b, hb, hB⟩ := hB
  refine ⟨a * b, fun χ => mul_ne_zero (ha χ) (hb χ), ?_⟩
  convert hA.tensor hB using 1
  funext χ
  simp only [Subalgebra.coe_mul, Pi.mul_apply, TensorProduct.map_smul_left,
    TensorProduct.map_smul_right, smul_smul, mul_comm]

namespace RationalOperatorContinuationData

variable {A : Ω → V →ₗ[ℂ] V'} {B : Λ → W →ₗ[ℂ] W'}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)

/-- Tensor the actual displayed numerator operators and multiply their
denominators. The original families may have different starting regions. -/
def tensor :
    RationalOperatorContinuationData (Ω ∩ Λ)
      (fun χ => TensorProduct.map (A ⟨χ.val, χ.property.1⟩)
        (B ⟨χ.val, χ.property.2⟩)) where
  denominator := p.denominator * q.denominator
  denominator_nonzero χ :=
    mul_ne_zero (p.denominator_nonzero ⟨χ.val, χ.property.1⟩)
      (q.denominator_nonzero ⟨χ.val, χ.property.2⟩)
  numerator χ := TensorProduct.map (p.numerator χ) (q.numerator χ)
  polynomial := p.polynomial.tensor q.polynomial
  clears χ := by
    rw [p.clears ⟨χ.val, χ.property.1⟩, q.clears ⟨χ.val, χ.property.2⟩]
    simp only [TensorProduct.map_smul_left, TensorProduct.map_smul_right,
      smul_smul, Subalgebra.coe_mul, Pi.mul_apply, mul_comm]

/-- The regular region of this presentation is exactly the intersection
of the two displayed regular regions. -/
@[simp]
theorem tensor_regularRegion :
    (p.tensor q).regularRegion = p.regularRegion ∩ q.regularRegion := by
  ext χ
  exact mul_ne_zero_iff

/-- Continuation of the displayed tensor numerator is the tensor of the
two independently continued displayed operators. -/
theorem tensor_continuedOperator
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    (p.tensor q).continuedOperator ⟨χ.val, by
        rw [tensor_regularRegion]
        exact χ.property⟩ =
      TensorProduct.map (p.continuedOperator ⟨χ.val, χ.property.1⟩)
        (q.continuedOperator ⟨χ.val, χ.property.2⟩) := by
  simp only [continuedOperator, tensor, Subalgebra.coe_mul, Pi.mul_apply,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul, mul_inv,
    mul_comm]

end RationalOperatorContinuationData

end Langlands.Plancherel.UnramifiedOperatorFamily
