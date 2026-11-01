import Langlands.HarmonicAnalysis.PartialFourierEquiv
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Group.GL.Maps
import Langlands.LocalField.Canonical
import Langlands.LocalField.Topology
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# JPSS Section 6.1: the special `(r+1,1)` tensor integral model

The raw scalar integral of JPSS Section 6.1, formula (8), in ambient rank `r + 2`
with lower blocks `(r + 1, 1)`. Test vectors are finite tensors of rectangular
Schwartz functions with vectors of the actual Whittaker coefficient image, and
`ρ₀` acts on the Schwartz factor only. The integral is the totalized Bochner
integral for a supplied measure; no convergence or model membership is asserted.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct

universe uF uV

section TestSpace

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V) (ℓ : glFunctionals ψ r σ)

/-- JPSS's `S(t-1 × t, F) ⊗ W(σ₁; ψ)` at `t = r + 2`: the algebraic complex tensor
product of rectangular Schwartz functions with the actual coefficient image of `ℓ`. -/
abbrev adjacentRankTestSpace :=
  SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F) ⊗[ℂ]
    (glCoefficientModel ψ r σ ℓ).toSubmodule

/-- The bilinear rule `(Φ, W) ↦ ((m, k) ↦ Φ(m) W(k))`. -/
def adjacentRankTestBilinear :
    SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F) →ₗ[ℂ]
      (glCoefficientModel ψ r σ ℓ).toSubmodule →ₗ[ℂ]
        (Matrix (Fin (r + 1)) (Fin (r + 2)) F → GeneralLinear (r + 1) F → ℂ) :=
  LinearMap.mk₂ ℂ (fun Φ W m k => Φ m * glModelFunction ψ r σ ℓ W k)
    (fun Φ₁ Φ₂ W => by
      funext m k
      simp only [Submodule.coe_add, Pi.add_apply, add_mul])
    (fun c Φ W => by
      funext m k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
    (fun Φ W₁ W₂ => by
      funext m k
      change Φ m * (W₁.val.val k + W₂.val.val k) = _
      simp only [Pi.add_apply, mul_add]
      rfl)
    (fun c Φ W => by
      funext m k
      change Φ m * (c * W.val.val k) = _
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
      rfl)

/-- The canonical evaluation of a test tensor at a rectangular matrix `m` and an
inner group element `k`, linear in the tensor. -/
def adjacentRankTestEvaluation :
    adjacentRankTestSpace ψ σ ℓ →ₗ[ℂ]
      (Matrix (Fin (r + 1)) (Fin (r + 2)) F → GeneralLinear (r + 1) F → ℂ) :=
  TensorProduct.lift (adjacentRankTestBilinear ψ σ ℓ)

@[simp] theorem adjacentRankTestEvaluation_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (k : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation ψ σ ℓ (Φ ⊗ₜ W) m k = Φ m * glModelFunction ψ r σ ℓ W k :=
  rfl

@[simp] theorem adjacentRankTestEvaluation_zero
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (k : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation ψ σ ℓ 0 m k = 0 := by
  rw [map_zero]
  rfl

theorem adjacentRankTestEvaluation_add (Ψ₁ Ψ₂ : adjacentRankTestSpace ψ σ ℓ)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (k : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation ψ σ ℓ (Ψ₁ + Ψ₂) m k =
      adjacentRankTestEvaluation ψ σ ℓ Ψ₁ m k + adjacentRankTestEvaluation ψ σ ℓ Ψ₂ m k := by
  rw [map_add]
  rfl

theorem adjacentRankTestEvaluation_smul (c : ℂ) (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (k : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation ψ σ ℓ (c • Ψ) m k =
      c * adjacentRankTestEvaluation ψ σ ℓ Ψ m k := by
  rw [map_smul]
  rfl

theorem adjacentRankTestEvaluation_sum {ι : Type*} (S : Finset ι)
    (Ψ : ι → adjacentRankTestSpace ψ σ ℓ)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (k : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation ψ σ ℓ (∑ i ∈ S, Ψ i) m k =
      ∑ i ∈ S, adjacentRankTestEvaluation ψ σ ℓ (Ψ i) m k := by
  rw [map_sum, Finset.sum_apply, Finset.sum_apply]

/-- Every test tensor is a finite sum of pure tensors. -/
theorem adjacentRankTestSpace_exists_sum_tmul (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    ∃ (n : ℕ) (Φ : Fin n → SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
      (W : Fin n → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      Ψ = ∑ j, Φ j ⊗ₜ W j :=
  TensorProduct.exists_sum_tmul_eq Ψ

/-- Induction over test tensors: a property of pure tensors that is stable under
addition holds for every test tensor (zero is the pure tensor `0 ⊗ₜ 0`). -/
@[elab_as_elim]
theorem adjacentRankTestSpace_induction {P : adjacentRankTestSpace ψ σ ℓ → Prop}
    (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (tmul : ∀ (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
      (W : (glCoefficientModel ψ r σ ℓ).toSubmodule), P (Φ ⊗ₜ W))
    (add : ∀ Ψ₁ Ψ₂, P Ψ₁ → P Ψ₂ → P (Ψ₁ + Ψ₂)) : P Ψ :=
  TensorProduct.inductionOn Ψ tmul add

/-- Evaluation of a finite sum of pure tensors. -/
theorem adjacentRankTestEvaluation_sum_tmul {n : ℕ}
    (Φ : Fin n → SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : Fin n → (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (k : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation ψ σ ℓ (∑ j, Φ j ⊗ₜ W j) m k =
      ∑ j, Φ j m * glModelFunction ψ r σ ℓ (W j) k := by
  rw [adjacentRankTestEvaluation_sum]
  rfl

end TestSpace

section Kernel

open Matrix

variable {F : Type uF} [Field F] {r : ℕ}

variable (F r) in
/-- JPSS's `ε`, the transpose of `η = (0, …, 0, 1)`: the last standard basis column
of length `r + 1`. -/
def adjacentRankEpsilon : Fin (r + 1) → F :=
  Pi.single (Fin.last r) 1

/-- The kernel matrix `[h, h^ι ε]` of formula (8), with `h^ι = ᵗ(h⁻¹)` the
published inverse transpose. -/
def adjacentRankKernelMatrix (h : GeneralLinear (r + 1) F) :
    Matrix (Fin (r + 1)) (Fin (r + 2)) F :=
  rectangularJoin h.val
    ((GeneralLinear.inverseTranspose (r + 1) F h).val *ᵥ adjacentRankEpsilon F r)

/-- `h^ι ε` is the last row of `h⁻¹`, read as a column. -/
theorem inverseTranspose_mulVec_adjacentRankEpsilon (h : GeneralLinear (r + 1) F)
    (i : Fin (r + 1)) :
    ((GeneralLinear.inverseTranspose (r + 1) F h).val *ᵥ adjacentRankEpsilon F r) i =
      (h⁻¹ : GeneralLinear (r + 1) F) (Fin.last r) i := by
  simp [adjacentRankEpsilon, Matrix.mulVec_single]

@[simp] theorem adjacentRankKernelMatrix_castSucc (h : GeneralLinear (r + 1) F)
    (i j : Fin (r + 1)) :
    adjacentRankKernelMatrix h i j.castSucc = h i j := by
  simp [adjacentRankKernelMatrix]

@[simp] theorem adjacentRankKernelMatrix_last (h : GeneralLinear (r + 1) F)
    (i : Fin (r + 1)) :
    adjacentRankKernelMatrix h i (Fin.last (r + 1)) =
      (h⁻¹ : GeneralLinear (r + 1) F) (Fin.last r) i := by
  rw [adjacentRankKernelMatrix, rectangularJoin_last,
    inverseTranspose_mulVec_adjacentRankEpsilon]

@[simp] theorem rectangularFirstColumns_adjacentRankKernelMatrix
    (h : GeneralLinear (r + 1) F) :
    rectangularFirstColumns (adjacentRankKernelMatrix h) = h.val := by
  ext i j
  exact adjacentRankKernelMatrix_castSucc h i j

@[simp] theorem rectangularLastColumn_adjacentRankKernelMatrix
    (h : GeneralLinear (r + 1) F) :
    rectangularLastColumn (adjacentRankKernelMatrix h) =
      fun i => (h⁻¹ : GeneralLinear (r + 1) F) (Fin.last r) i := by
  funext i
  exact adjacentRankKernelMatrix_last h i

/-- For `r = 0` (inner `GL₁`, ambient `GL₂`) the kernel is the row `[h, h⁻¹]`. -/
theorem adjacentRankKernelMatrix_rankZero (h : GeneralLinear 1 F) :
    adjacentRankKernelMatrix h = !![h 0 0, (h⁻¹ : GeneralLinear 1 F) 0 0] := by
  ext i j
  fin_cases i
  fin_cases j
  · exact adjacentRankKernelMatrix_castSucc h 0 0
  · exact adjacentRankKernelMatrix_last h 0

end Kernel

section Action

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F) (hself : IsSelfDual ψ ν)
  {r : ℕ} (σ : Representation ℂ (GeneralLinear (r + 1) F) V) (ℓ : glFunctionals ψ r σ)

/-- JPSS's `ρ₀` extended to model-valued Schwartz functions: the published
`rectangularRho0` on the Schwartz factor, the identity on the model factor. -/
def adjacentRankRho0 :
    Representation ℂ (GeneralLinear (r + 2) F) (adjacentRankTestSpace ψ σ ℓ) where
  toFun g := TensorProduct.map (rectangularRho0 ψ ν (r + 1) hself g) LinearMap.id
  map_one' := by
    apply TensorProduct.ext'
    intro Φ W
    simp
  map_mul' g h := by
    apply TensorProduct.ext'
    intro Φ W
    simp

theorem adjacentRankRho0_apply (g : GeneralLinear (r + 2) F) :
    adjacentRankRho0 ψ ν hself σ ℓ g =
      TensorProduct.map (rectangularRho0 ψ ν (r + 1) hself g) LinearMap.id :=
  rfl

@[simp] theorem adjacentRankRho0_tmul (g : GeneralLinear (r + 2) F)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    adjacentRankRho0 ψ ν hself σ ℓ g (Φ ⊗ₜ W) = rectangularRho0 ψ ν (r + 1) hself g Φ ⊗ₜ W :=
  rfl

@[simp] theorem adjacentRankRho0_one (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankRho0 ψ ν hself σ ℓ 1 Ψ = Ψ := by
  rw [map_one]
  rfl

theorem adjacentRankRho0_mul (g h : GeneralLinear (r + 2) F)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankRho0 ψ ν hself σ ℓ (g * h) Ψ =
      adjacentRankRho0 ψ ν hself σ ℓ g (adjacentRankRho0 ψ ν hself σ ℓ h Ψ) := by
  rw [map_mul]
  rfl

end Action

section Integral

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F) (hself : IsSelfDual ψ ν)
  {r : ℕ} (σ : Representation ℂ (GeneralLinear (r + 1) F) V) (ℓ : glFunctionals ψ r σ)
  (abv : AbsoluteValue F ℝ) (χ : Quasicharacter F)

/-- The integrand of formula (8) at ambient rank `r + 2`:
`(ρ₀(g)Ψ)[h, h^ι ε; h⁻¹] χ(det h) |det h|^(r/2)`. -/
def adjacentRankModelIntegrand (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F) (h : GeneralLinear (r + 1) F) : ℂ :=
  adjacentRankTestEvaluation ψ σ ℓ (adjacentRankRho0 ψ ν hself σ ℓ g Ψ)
      (adjacentRankKernelMatrix h) h⁻¹ *
    (χ (GeneralLinear.determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)

variable [MeasurableSpace (GeneralLinear (r + 1) F)]
  (η : Measure (GeneralLinear (r + 1) F))

/-- Integrability of the formula (8) integrand for the supplied inner measure. -/
def AdjacentRankModelConverges (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F) : Prop :=
  Integrable (fun h => adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ g h) η

/-- The raw formula (8) value `χ(det g) |det g|^((r+1)/2) ∫ I(Ψ,g,h) dη(h)`,
a totalized Bochner integral. -/
def adjacentRankModelIntegral (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F) : ℂ :=
  (χ (GeneralLinear.determinant g) : ℂ) * determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
    ∫ h, adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ g h ∂η

end Integral

section IntegralLaws

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ψ : UnitaryAdditiveCharacter F} {ν : AdditiveHaarMeasure F} {hself : IsSelfDual ψ ν}
  {r : ℕ} {σ : Representation ℂ (GeneralLinear (r + 1) F) V} {ℓ : glFunctionals ψ r σ}
  {abv : AbsoluteValue F ℝ} {χ : Quasicharacter F} {g : GeneralLinear (r + 2) F}

@[simp] theorem adjacentRankModelIntegrand_zero :
    adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ 0 g = 0 := by
  funext h
  simp [adjacentRankModelIntegrand]

theorem adjacentRankModelIntegrand_add (Ψ₁ Ψ₂ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ (Ψ₁ + Ψ₂) g =
      adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ₁ g +
        adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ₂ g := by
  funext h
  simp only [adjacentRankModelIntegrand, map_add, adjacentRankTestEvaluation_add,
    Pi.add_apply]
  ring

theorem adjacentRankModelIntegrand_smul (c : ℂ) (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ (c • Ψ) g =
      c • adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ Ψ g := by
  funext h
  simp only [adjacentRankModelIntegrand, map_smul, adjacentRankTestEvaluation_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem adjacentRankModelIntegrand_sum {ι : Type*} (S : Finset ι)
    (Ψ : ι → adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ (∑ i ∈ S, Ψ i) g =
      ∑ i ∈ S, adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ (Ψ i) g := by
  funext h
  simp only [adjacentRankModelIntegrand, map_sum, adjacentRankTestEvaluation_sum,
    Finset.sum_apply, Finset.sum_mul]

/-- The integrand at a pure tensor. -/
theorem adjacentRankModelIntegrand_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) (h : GeneralLinear (r + 1) F) :
    adjacentRankModelIntegrand ψ ν hself σ ℓ abv χ (Φ ⊗ₜ W) g h =
      rectangularRho0 ψ ν (r + 1) hself g Φ (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W h⁻¹ *
        (χ (GeneralLinear.determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2) :=
  rfl

variable [MeasurableSpace (GeneralLinear (r + 1) F)] {η : Measure (GeneralLinear (r + 1) F)}

theorem adjacentRankModelConverges_zero :
    AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η 0 g := by
  rw [AdjacentRankModelConverges, adjacentRankModelIntegrand_zero]
  exact integrable_zero _ _ _

theorem AdjacentRankModelConverges.add {Ψ₁ Ψ₂ : adjacentRankTestSpace ψ σ ℓ}
    (h₁ : AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η Ψ₁ g)
    (h₂ : AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η Ψ₂ g) :
    AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η (Ψ₁ + Ψ₂) g := by
  rw [AdjacentRankModelConverges, adjacentRankModelIntegrand_add]
  exact Integrable.add h₁ h₂

theorem AdjacentRankModelConverges.smul {Ψ : adjacentRankTestSpace ψ σ ℓ}
    (hΨ : AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η Ψ g) (c : ℂ) :
    AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η (c • Ψ) g := by
  rw [AdjacentRankModelConverges, adjacentRankModelIntegrand_smul]
  exact Integrable.smul c hΨ

theorem adjacentRankModelConverges_sum {ι : Type*} (S : Finset ι)
    {Ψ : ι → adjacentRankTestSpace ψ σ ℓ}
    (hΨ : ∀ i ∈ S, AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η (Ψ i) g) :
    AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η (∑ i ∈ S, Ψ i) g := by
  rw [AdjacentRankModelConverges, adjacentRankModelIntegrand_sum]
  exact integrable_finsetSum' S hΨ

@[simp] theorem adjacentRankModelIntegral_zero :
    adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η 0 g = 0 := by
  simp [adjacentRankModelIntegral]

/-- Additivity at a fixed `g`, assuming integrability of both summands. -/
theorem adjacentRankModelIntegral_add {Ψ₁ Ψ₂ : adjacentRankTestSpace ψ σ ℓ}
    (h₁ : AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η Ψ₁ g)
    (h₂ : AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η Ψ₂ g) :
    adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η (Ψ₁ + Ψ₂) g =
      adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η Ψ₁ g +
        adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η Ψ₂ g := by
  unfold adjacentRankModelIntegral
  rw [adjacentRankModelIntegrand_add]
  simp only [Pi.add_apply]
  rw [integral_add h₁ h₂, mul_add]

theorem adjacentRankModelIntegral_smul (c : ℂ) (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η (c • Ψ) g =
      c * adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η Ψ g := by
  unfold adjacentRankModelIntegral
  rw [adjacentRankModelIntegrand_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  ring

/-- Finite additivity, assuming integrability of every summand at the fixed `g`. -/
theorem adjacentRankModelIntegral_sum {ι : Type*} (S : Finset ι)
    {Ψ : ι → adjacentRankTestSpace ψ σ ℓ}
    (hΨ : ∀ i ∈ S, AdjacentRankModelConverges ψ ν hself σ ℓ abv χ η (Ψ i) g) :
    adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η (∑ i ∈ S, Ψ i) g =
      ∑ i ∈ S, adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η (Ψ i) g := by
  unfold adjacentRankModelIntegral
  rw [adjacentRankModelIntegrand_sum]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum S hΨ, Finset.mul_sum]

/-- The raw integral at a pure tensor. -/
theorem adjacentRankModelIntegral_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    adjacentRankModelIntegral ψ ν hself σ ℓ abv χ η (Φ ⊗ₜ W) g =
      (χ (GeneralLinear.determinant g) : ℂ) *
        determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
        ∫ h, rectangularRho0 ψ ν (r + 1) hself g Φ (adjacentRankKernelMatrix h) *
          glModelFunction ψ r σ ℓ W h⁻¹ *
          (χ (GeneralLinear.determinant h) : ℂ) *
          determinantWeight abv h ((r : ℂ) / 2) ∂η :=
  rfl

end IntegralLaws

/-! ## Canonical p-adic specializations

For `F : PadicField p` we use its canonical topology, the Borel structures, the
normalized absolute value and the shared Haar measure `generalLinearHaar F.Carrier r`
on the inner `GL_(r+1)`, giving `GL_(r+1)(O_F)` mass one. The character `ψ`, the
scalar Haar measure `ν`, its self-duality, `σ`, `ℓ` and `χ` remain supplied. -/

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (ℓ : glFunctionals ψ r σ)
  (χ : Quasicharacter F.Carrier)

/-- The formula (8) integrand with the canonical normalized absolute value. -/
def adjacentRankModelIntegrand (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F.Carrier) (h : GeneralLinear (r + 1) F.Carrier) : ℂ :=
  RankinSelberg.adjacentRankModelIntegrand ψ ν hself σ ℓ
    (normalizedAbsoluteValue F.canonicalTopologicalData) χ Ψ g h

/-- Convergence for the shared Haar measure on the inner `GL_(r+1)`. -/
def AdjacentRankModelConverges (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F.Carrier) : Prop :=
  RankinSelberg.AdjacentRankModelConverges ψ ν hself σ ℓ
    (normalizedAbsoluteValue F.canonicalTopologicalData) χ (generalLinearHaar F.Carrier r) Ψ g

/-- The raw formula (8) integral for the shared Haar measure on the inner `GL_(r+1)`. -/
def adjacentRankModelIntegral (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F.Carrier) : ℂ :=
  RankinSelberg.adjacentRankModelIntegral ψ ν hself σ ℓ
    (normalizedAbsoluteValue F.canonicalTopologicalData) χ (generalLinearHaar F.Carrier r) Ψ g

end Padic

end Langlands.RankinSelberg
