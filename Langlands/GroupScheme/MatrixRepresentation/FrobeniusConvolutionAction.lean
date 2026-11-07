import Langlands.GroupScheme.MatrixRepresentation.FrobeniusDistributionAlgebra
import Mathlib.RingTheory.Coalgebra.Convolution

/-! # Actual Frobenius distribution convolution and its original action -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionAction

open FrobeniusCoordinateModel FrobeniusOrderedDistributions FrobeniusOriginUniversality
open FrobeniusDistributionAlgebra

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The full dual of the actual Frobenius quotient, with its inherited
convolution algebra structure. -/
abbrev DistributionAlgebra := WithConv (Module.Dual k (quotientAlgebra G p r))

local notation "Q" => quotientAlgebra G p r
local notation "D" => DistributionAlgebra (G := G) p r

variable {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- Coefficients of the original representation at the genuine quotient point. -/
def coefficientMatrix : Matrix n n Q :=
  (ρ.affineMatrix Q (quotientPoint G p r) : Matrix n n Q)

theorem coefficientMatrix_apply (i j : n) :
    coefficientMatrix p r ρ i j =
      quotientMap G p r (TorusUnipotence.coeffMatrix ρ i j) :=
  congrArg (fun M : Matrix n n Q => M i j) (affineMatrix_quotientPoint p r ρ)

/-- The actual quotient coefficients satisfy the matrix coproduct identity. -/
theorem comul_coefficientMatrix (i j : n) :
    Coalgebra.comul (R := k) (coefficientMatrix p r ρ i j) =
      ∑ l, coefficientMatrix p r ρ i l ⊗ₜ[k] coefficientMatrix p r ρ l j := by
  rw [coefficientMatrix_apply, comul_quotientMap]
  change Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r)
    (TorusUnipotence.coordComul G (TorusUnipotence.coeffMatrix ρ i j)) = _
  rw [TorusUnipotence.coordComul_coeffMatrix, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, coefficientMatrix_apply]

/-- The actual quotient coefficient counit is the identity matrix. -/
theorem counit_coefficientMatrix (i j : n) :
    Coalgebra.counit (R := k) (coefficientMatrix p r ρ i j) =
      (1 : Matrix n n k) i j := by
  rw [coefficientMatrix_apply, counit_quotientMap]
  exact TorusUnipotence.coordCounit_coeffMatrix ρ i j

/-- The existing original distribution action, with convolution in its domain. -/
def actionLinear : D →ₗ[k] Module.End k (n → k) :=
  (distributionAction p r ρ).comp (WithConv.linearEquiv k _).toLinearMap

@[simp]
theorem actionLinear_apply (f : D) :
    actionLinear p r ρ f = distributionAction p r ρ f.ofConv := rfl

/-- The convolution unit acts by the identity on the original representation. -/
theorem actionLinear_one : actionLinear p r ρ 1 = 1 := by
  have hM : (coefficientMatrix p r ρ).map (1 : D).ofConv = 1 := by
    ext i j
    change (1 : D) (coefficientMatrix p r ρ i j) = _
    rw [LinearMap.convOne_apply, counit_coefficientMatrix]
    rfl
  change Matrix.toLin' ((coefficientMatrix p r ρ).map (1 : D).ofConv) = 1
  rw [hM, Matrix.toLin'_one]
  rfl

/-- Convolution acts by composition, with the original matrix factor order. -/
theorem actionLinear_mul (f g : D) :
    actionLinear p r ρ (f * g) = actionLinear p r ρ f * actionLinear p r ρ g := by
  have hM : (coefficientMatrix p r ρ).map (f * g).ofConv =
      (coefficientMatrix p r ρ).map f.ofConv * (coefficientMatrix p r ρ).map g.ofConv := by
    ext i j
    change (f * g) (coefficientMatrix p r ρ i j) =
      ∑ l, f (coefficientMatrix p r ρ i l) * g (coefficientMatrix p r ρ l j)
    rw [LinearMap.convMul_apply, comul_coefficientMatrix]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply]
  change Matrix.toLin' ((coefficientMatrix p r ρ).map (f * g).ofConv) =
    (Matrix.toLin' ((coefficientMatrix p r ρ).map f.ofConv)).comp
      (Matrix.toLin' ((coefficientMatrix p r ρ).map g.ofConv))
  rw [hM, Matrix.toLin'_mul]

/-- A unital algebra representation of the actual quotient convolution dual. -/
def actionAlgHom : D →ₐ[k] Module.End k (n → k) :=
  AlgHom.ofLinearMap (actionLinear p r ρ) (actionLinear_one p r ρ)
    (actionLinear_mul p r ρ)

@[simp]
theorem actionAlgHom_apply (f : D) :
    actionAlgHom p r ρ f = distributionAction p r ρ f.ofConv := rfl

/-- The full distribution operator range is the underlying submodule of the
actual action algebra image. -/
theorem range_distributionAction :
    LinearMap.range (distributionAction p r ρ) =
      (actionAlgHom p r ρ).range.toSubmodule := by
  ext f
  constructor
  · rintro ⟨ℓ, rfl⟩
    exact ⟨WithConv.toConv ℓ, rfl⟩
  · rintro ⟨ℓ, rfl⟩
    exact ⟨ℓ.ofConv, rfl⟩

/-- The original vector lies in its intrinsic Frobenius-origin orbit span. -/
theorem mem_originOrbitSpan (v : n → k) : v ∈ originOrbitSpan p r ρ v := by
  rw [originOrbitSpan_eq_range]
  refine ⟨(1 : D).ofConv, ?_⟩
  change actionLinear p r ρ 1 v = v
  rw [actionLinear_one]
  rfl

/-- Intrinsic Frobenius-origin orbit spans are stable under every distribution
of the actual quotient, with no ordered coordinate hypothesis. -/
theorem distributionAction_mem_originOrbitSpan (v : n → k)
    (ℓ : Module.Dual k Q) {w : n → k} (hw : w ∈ originOrbitSpan p r ρ v) :
    distributionAction p r ρ ℓ w ∈ originOrbitSpan p r ρ v := by
  rw [originOrbitSpan_eq_range] at hw ⊢
  rcases hw with ⟨ell2, rfl⟩
  refine ⟨(WithConv.toConv ℓ * WithConv.toConv ell2 : D).ofConv, ?_⟩
  exact congrArg (fun f : Module.End k (n → k) => f v)
    (actionLinear_mul p r ρ (WithConv.toConv ℓ) (WithConv.toConv ell2))

/-- Equivalently, the orbit span is stable under contraction at every original
intrinsic origin point over every commutative test algebra. -/
theorem originPoints_mem_originOrbitSpan (v : n → k)
    (A : CommAlgCat.{u} k) (g : G.affinePoints A) (hg : IsOriginPoint p r A g)
    {w : n → k} (hw : w ∈ originOrbitSpan p r ρ v) (ℓ : A →ₗ[k] k) :
    (fun i => ℓ (ρ.affineAction A g (fun j => algebraMap k A (w j)) i)) ∈
      originOrbitSpan p r ρ v := by
  rw [contract_affineAction p r ρ A g hg]
  exact distributionAction_mem_originOrbitSpan p r ρ v _ hw

/-- The intrinsic orbit span is contained in every distribution-stable subspace
containing the original vector. -/
theorem originOrbitSpan_le (v : n → k) (W : Submodule k (n → k)) (hv : v ∈ W)
    (hW : ∀ ℓ : Module.Dual k Q, ∀ w ∈ W, distributionAction p r ρ ℓ w ∈ W) :
    originOrbitSpan p r ρ v ≤ W := by
  rw [originOrbitSpan_eq_range]
  rintro w ⟨ℓ, rfl⟩
  exact hW ℓ v hv

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionAction
