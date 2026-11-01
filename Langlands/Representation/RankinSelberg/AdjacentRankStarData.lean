import Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.HarmonicAnalysis.RectangularFourierEquiv

/-!
# The JPSS adjacent-rank tensor star map and sign matrix

The source model uses the inverse additive character; the full Fourier factor
uses plus `ψ`. These constructions concern the algebraic tensor space only.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct

universe uF uV

section Functional

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {r : ℕ}
  (ψ : UnitaryAdditiveCharacter F)
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)

/-- The Weyl-translated functional on the original carrier, with target character
`ψ` and the actual inverse-transpose pullback representation. -/
def adjacentRankStarFunctional (ℓ : glFunctionals (ψ.scale (-1)) r σ) :
    glFunctionals ψ r (inverseTransposePullback σ) :=
  functionalsCongr (inverseStandardCharacter_scale_neg_one ψ r)
    (dualFunctional (ψ.scale (-1)) σ ℓ)

@[simp] theorem adjacentRankStarFunctional_val
    (ℓ : glFunctionals (ψ.scale (-1)) r σ) :
    (adjacentRankStarFunctional ψ σ ℓ).val =
      ℓ.val.comp (σ (GeneralLinear.weylLong (r + 1) F)) := rfl

@[simp] theorem adjacentRankStarFunctional_apply
    (ℓ : glFunctionals (ψ.scale (-1)) r σ) (v : V) :
    (adjacentRankStarFunctional ψ σ ℓ).val v =
      ℓ.val (σ (GeneralLinear.weylLong (r + 1) F) v) := rfl

theorem adjacentRankStarFunctional_ne_zero
    (ℓ : glFunctionals (ψ.scale (-1)) r σ) (hℓ : ℓ.val ≠ 0) :
    (adjacentRankStarFunctional ψ σ ℓ).val ≠ 0 :=
  dualFunctional_nonzero (ψ.scale (-1)) σ ℓ hℓ

end Functional

section Model

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {r : ℕ}

/-- Equality of characters transports an actual coefficient image and leaves its
underlying functions unchanged. -/
private def coefficientCharacterEquiv
    {θ θ' : GeneralLinear.upperUnipotent (r + 1) F →* ℂˣ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (e : θ = θ') (ℓ : functionals (GeneralLinear.upperUnipotent (r + 1) F) θ σ) :
    (coefficientModel σ ℓ).toSubmodule ≃ₗ[ℂ]
      (coefficientModel σ (functionalsCongr e ℓ)).toSubmodule := by
  cases e
  exact LinearEquiv.refl ℂ _

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem coefficientCharacterEquiv_apply
    {θ θ' : GeneralLinear.upperUnipotent (r + 1) F →* ℂˣ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (e : θ = θ') (ℓ : functionals (GeneralLinear.upperUnipotent (r + 1) F) θ σ)
    (W : (coefficientModel σ ℓ).toSubmodule) (h : GeneralLinear (r + 1) F) :
    (coefficientCharacterEquiv σ e ℓ W).val.val h = W.val.val h := by
  cases e
  rfl

variable (ψ : UnitaryAdditiveCharacter F)
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals (ψ.scale (-1)) r σ)

/-- Weyl/inverse-transpose precomposition between the actual coefficient images.
No injectivity of the coefficient map is assumed. -/
def adjacentRankStarModelEquiv :
    (glCoefficientModel (ψ.scale (-1)) r σ ℓ).toSubmodule ≃ₗ[ℂ]
      (glCoefficientModel ψ r (inverseTransposePullback σ)
        (adjacentRankStarFunctional ψ σ ℓ)).toSubmodule :=
  (dualModelEquiv (ψ.scale (-1)) σ ℓ).toLinearEquiv.trans
    (coefficientCharacterEquiv (inverseTransposePullback σ)
      (inverseStandardCharacter_scale_neg_one ψ r)
      (dualFunctional (ψ.scale (-1)) σ ℓ))

@[simp] theorem adjacentRankStarModelEquiv_apply
    (W : (glCoefficientModel (ψ.scale (-1)) r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F) :
    glModelFunction ψ r (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ)
        (adjacentRankStarModelEquiv ψ σ ℓ W) h =
      glModelFunction (ψ.scale (-1)) r σ ℓ W
          (GeneralLinear.weylLong (r + 1) F * GeneralLinear.inverseTranspose (r + 1) F h) := by
  exact coefficientCharacterEquiv_apply (inverseTransposePullback σ)
    (inverseStandardCharacter_scale_neg_one ψ r) (dualFunctional (ψ.scale (-1)) σ ℓ)
    (dualModelLinearMap (ψ.scale (-1)) σ ℓ W) h

@[simp] theorem adjacentRankStarModelEquiv_symm_apply
    (W : (glCoefficientModel ψ r (inverseTransposePullback σ)
      (adjacentRankStarFunctional ψ σ ℓ)).toSubmodule)
    (h : GeneralLinear (r + 1) F) :
    glModelFunction (ψ.scale (-1)) r σ ℓ
        ((adjacentRankStarModelEquiv ψ σ ℓ).symm W) h =
      glModelFunction ψ r (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ) W
        (GeneralLinear.weylLong (r + 1) F * GeneralLinear.inverseTranspose (r + 1) F h) := by
  have he := adjacentRankStarModelEquiv_apply ψ σ ℓ
    ((adjacentRankStarModelEquiv ψ σ ℓ).symm W)
    (GeneralLinear.weylInverseTranspose (r + 1) F h)
  simpa only [LinearEquiv.apply_symm_apply, ← GeneralLinear.weylInverseTranspose_apply,
    GeneralLinear.weylInverseTranspose_involutive] using he.symm

/-- The vector `v` is unchanged when its coefficient is transformed. -/
@[simp] theorem adjacentRankStarModelEquiv_modelMap (v : V) :
    adjacentRankStarModelEquiv ψ σ ℓ (modelMap σ ℓ v) =
      modelMap (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ) v := by
  apply Subtype.ext
  apply Subtype.ext
  funext h
  change glModelFunction ψ r (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ)
      (adjacentRankStarModelEquiv ψ σ ℓ (modelMap σ ℓ v)) h = _
  rw [adjacentRankStarModelEquiv_apply]
  change ℓ.val (σ (GeneralLinear.weylLong (r + 1) F *
      GeneralLinear.inverseTranspose (r + 1) F h) v) = _
  rw [map_mul, Module.End.mul_apply]
  rfl

end Model

section Tensor

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]
  [LocallyCompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {r : ℕ}
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F) (hself : IsSelfDual ψ ν)
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals (ψ.scale (-1)) r σ)

/-- JPSS Section 6.2 at `t = r + 2`: full plus Fourier transform tensored with
the actual inverse-transpose coefficient-image equivalence. -/
def adjacentRankStarEquiv :
    adjacentRankTestSpace (ψ.scale (-1)) σ ℓ ≃ₗ[ℂ]
      adjacentRankTestSpace ψ (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ) :=
  TensorProduct.congr (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself)
    (adjacentRankStarModelEquiv ψ σ ℓ)

@[simp] theorem adjacentRankStarEquiv_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel (ψ.scale (-1)) r σ ℓ).toSubmodule) :
    adjacentRankStarEquiv ψ ν hself σ ℓ (Φ ⊗ₜ W) =
      rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ ⊗ₜ
        adjacentRankStarModelEquiv ψ σ ℓ W := rfl

@[simp] theorem adjacentRankStarEquiv_symm_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r (inverseTransposePullback σ)
      (adjacentRankStarFunctional ψ σ ℓ)).toSubmodule) :
    (adjacentRankStarEquiv ψ ν hself σ ℓ).symm (Φ ⊗ₜ W) =
      (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself).symm Φ ⊗ₜ
        (adjacentRankStarModelEquiv ψ σ ℓ).symm W := rfl

@[simp] theorem adjacentRankStarEquiv_zero :
    adjacentRankStarEquiv ψ ν hself σ ℓ 0 = 0 :=
  map_zero _

theorem adjacentRankStarEquiv_add (Ψ₁ Ψ₂ : adjacentRankTestSpace (ψ.scale (-1)) σ ℓ) :
    adjacentRankStarEquiv ψ ν hself σ ℓ (Ψ₁ + Ψ₂) =
      adjacentRankStarEquiv ψ ν hself σ ℓ Ψ₁ + adjacentRankStarEquiv ψ ν hself σ ℓ Ψ₂ :=
  map_add _ _ _

theorem adjacentRankStarEquiv_smul (c : ℂ)
    (Ψ : adjacentRankTestSpace (ψ.scale (-1)) σ ℓ) :
    adjacentRankStarEquiv ψ ν hself σ ℓ (c • Ψ) =
      c • adjacentRankStarEquiv ψ ν hself σ ℓ Ψ :=
  map_smul _ _ _

theorem adjacentRankStarEquiv_sum {ι : Type*} (S : Finset ι)
    (Ψ : ι → adjacentRankTestSpace (ψ.scale (-1)) σ ℓ) :
    adjacentRankStarEquiv ψ ν hself σ ℓ (∑ i ∈ S, Ψ i) =
      ∑ i ∈ S, adjacentRankStarEquiv ψ ν hself σ ℓ (Ψ i) :=
  map_sum _ _ _

/-- Evaluation of the forward map on a pure tensor, with plus `ψ`. -/
theorem adjacentRankStarEquiv_tmul_evaluation
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel (ψ.scale (-1)) r σ ℓ).toSubmodule)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (h : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation ψ (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ)
        (adjacentRankStarEquiv ψ ν hself σ ℓ (Φ ⊗ₜ W)) m h =
      rectangularFourierIntegral ψ ν Φ m *
        glModelFunction (ψ.scale (-1)) r σ ℓ W
          (GeneralLinear.weylLong (r + 1) F * GeneralLinear.inverseTranspose (r + 1) F h) := by
  rw [adjacentRankStarEquiv_tmul, adjacentRankTestEvaluation_tmul,
    rectangularFourierEquiv_apply, adjacentRankStarModelEquiv_apply]

/-- The inverse uses the same plus integral at `-m`, with no second self-duality premise. -/
theorem adjacentRankStarEquiv_symm_tmul_evaluation
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r (inverseTransposePullback σ)
      (adjacentRankStarFunctional ψ σ ℓ)).toSubmodule)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F) (h : GeneralLinear (r + 1) F) :
    adjacentRankTestEvaluation (ψ.scale (-1)) σ ℓ
        ((adjacentRankStarEquiv ψ ν hself σ ℓ).symm (Φ ⊗ₜ W)) m h =
      rectangularFourierIntegral ψ ν Φ (-m) *
        glModelFunction ψ r (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ) W
          (GeneralLinear.weylLong (r + 1) F * GeneralLinear.inverseTranspose (r + 1) F h) := by
  rw [adjacentRankStarEquiv_symm_tmul, adjacentRankTestEvaluation_tmul,
    rectangularFourierEquiv_symm_apply, adjacentRankStarModelEquiv_symm_apply]

end Tensor

section SignMatrix

variable (F : Type uF) [CommRing F] (r : ℕ)

/-- The diagonal entries of the JPSS sign matrix, including the final `+1`. -/
def adjacentRankZetaDiagonal : Fin (r + 2) → F :=
  Fin.snoc (fun _ : Fin (r + 1) => (-1 : F)) 1

@[simp] theorem adjacentRankZetaDiagonal_castSucc (i : Fin (r + 1)) :
    adjacentRankZetaDiagonal F r i.castSucc = -1 := by
  simp [adjacentRankZetaDiagonal]

@[simp] theorem adjacentRankZetaDiagonal_last :
    adjacentRankZetaDiagonal F r (Fin.last (r + 1)) = 1 := by
  simp [adjacentRankZetaDiagonal]

private theorem adjacentRankZetaDiagonal_mul_self (i : Fin (r + 2)) :
    adjacentRankZetaDiagonal F r i * adjacentRankZetaDiagonal F r i = 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- The actual matrix unit `diag(-1, ..., -1, 1)` in ambient rank `r + 2`.
Its inverse is constructed explicitly and is the same diagonal matrix. -/
def adjacentRankZeta : GeneralLinear (r + 2) F where
  val := Matrix.diagonal (adjacentRankZetaDiagonal F r)
  inv := Matrix.diagonal (adjacentRankZetaDiagonal F r)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact adjacentRankZetaDiagonal_mul_self F r i
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact adjacentRankZetaDiagonal_mul_self F r i

@[simp] theorem adjacentRankZeta_val :
    (adjacentRankZeta F r).val = Matrix.diagonal (adjacentRankZetaDiagonal F r) := rfl

theorem adjacentRankZeta_entry (i j : Fin (r + 2)) :
    adjacentRankZeta F r i j = if i = j then adjacentRankZetaDiagonal F r i else 0 := by
  simp [adjacentRankZeta, Matrix.diagonal_apply]

@[simp] theorem adjacentRankZeta_diagonal_castSucc (i : Fin (r + 1)) :
    adjacentRankZeta F r i.castSucc i.castSucc = -1 := by
  simp [adjacentRankZeta_entry]

@[simp] theorem adjacentRankZeta_diagonal_last :
    adjacentRankZeta F r (Fin.last (r + 1)) (Fin.last (r + 1)) = 1 := by
  simp [adjacentRankZeta_entry]

theorem adjacentRankZeta_offDiagonal (i j : Fin (r + 2)) (hij : i ≠ j) :
    adjacentRankZeta F r i j = 0 := by
  simp [adjacentRankZeta_entry, hij]

@[simp] theorem adjacentRankZeta_inv :
    (adjacentRankZeta F r)⁻¹ = adjacentRankZeta F r := by
  apply Units.ext
  rfl

@[simp] theorem adjacentRankZeta_mul_self :
    adjacentRankZeta F r * adjacentRankZeta F r = 1 := by
  rw [← adjacentRankZeta_inv F r]
  exact inv_mul_cancel _

@[simp] theorem adjacentRankZeta_sq : adjacentRankZeta F r ^ 2 = 1 := by
  rw [pow_two, adjacentRankZeta_mul_self]

@[simp] theorem adjacentRankZeta_inverseTranspose :
    GeneralLinear.inverseTranspose (r + 2) F (adjacentRankZeta F r) =
      adjacentRankZeta F r := by
  apply Units.ext
  rw [GeneralLinear.inverseTranspose_coe, adjacentRankZeta_inv, adjacentRankZeta_val,
    Matrix.diagonal_transpose]

theorem adjacentRankZeta_det :
    Matrix.det (adjacentRankZeta F r).val = (-1 : F) ^ (r + 1) := by
  rw [adjacentRankZeta_val, Matrix.det_diagonal, Fin.prod_univ_castSucc]
  simp

/-- Ambient rank two is included: at `r = 0` the sign matrix is `diag(-1, 1)`. -/
theorem adjacentRankZeta_rankZero :
    (adjacentRankZeta F 0).val = !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjacentRankZeta_entry, adjacentRankZetaDiagonal, Fin.snoc]

end SignMatrix

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

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {r : ℕ}
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hself : IsSelfDual ψ ν)
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals (ψ.scale (-1)) r σ)

/-- The same tensor equivalence for the canonical topology of every supplied
p-adic field; the coefficient carrier retains its independent universe. -/
def adjacentRankStarEquiv :
    adjacentRankTestSpace (ψ.scale (-1)) σ ℓ ≃ₗ[ℂ]
      adjacentRankTestSpace ψ (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ) :=
  RankinSelberg.adjacentRankStarEquiv ψ ν hself σ ℓ

theorem adjacentRankStarEquiv_tmul_evaluation
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel (ψ.scale (-1)) r σ ℓ).toSubmodule)
    (m : Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)
    (h : GeneralLinear (r + 1) F.Carrier) :
    adjacentRankTestEvaluation ψ (inverseTransposePullback σ) (adjacentRankStarFunctional ψ σ ℓ)
        (adjacentRankStarEquiv F ψ ν hself σ ℓ (Φ ⊗ₜ W)) m h =
      rectangularFourierIntegral ψ ν Φ m *
        glModelFunction (ψ.scale (-1)) r σ ℓ W
          (GeneralLinear.weylLong (r + 1) F.Carrier *
            GeneralLinear.inverseTranspose (r + 1) F.Carrier h) :=
  RankinSelberg.adjacentRankStarEquiv_tmul_evaluation ψ ν hself σ ℓ Φ W m h

end Padic

end Langlands.RankinSelberg
