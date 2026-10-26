import Langlands.Representation.RankinSelberg.RankOneExtensionTransport
import Langlands.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.Group.GL.RankMaps
import Langlands.HarmonicAnalysis.RowFourier
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Concrete section, tensor and matrix data for the early JPSS Lemma 5.5 argument. -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis

universe uF uW

section Tensor

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

local instance : ∀ i : Fin 2,
    AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) :=
  fun i => Shahidi.pairCarrier.instAddCommGroup i.rev

local instance : ∀ i : Fin 2,
    Module ℂ (rankOneExtensionLowerCarrier (W := W) i) :=
  fun i => Shahidi.pairCarrier.instModule ℂ i.rev

/-- The actual inducing tensor space, in the reversed block order `(W, ULift ℂ)`. -/
abbrev rankOneExtensionLowerTensor :=
  PiTensorProduct ℂ (rankOneExtensionLowerCarrier (W := W))

/-- Pure tensors in the exact reversed carrier used by the lower induction. -/
def rankOneExtensionLowerPureTensor (w : W) (z : ULift.{uW} ℂ) :
    rankOneExtensionLowerTensor (W := W) :=
  PiTensorProduct.reindex ℂ (Shahidi.pairCarrier (ULift.{uW} ℂ) W) Fin.revPerm
    (Shahidi.pairTensor z w)

/-- Contract the large factor with `ℓ` and the scalar factor with `ULift.down`. -/
def rankOneExtensionTensorContraction (ℓ : W →ₗ[ℂ] ℂ) :
    rankOneExtensionLowerTensor (W := W) →ₗ[ℂ] ℂ :=
  (Shahidi.pairFunctional ULift.moduleEquiv.toLinearMap ℓ).comp
    (PiTensorProduct.reindex ℂ (Shahidi.pairCarrier (ULift.{uW} ℂ) W)
      Fin.revPerm).symm.toLinearMap

@[simp] theorem rankOneExtensionTensorContraction_pure
    (ℓ : W →ₗ[ℂ] ℂ) (w : W) (z : ULift.{uW} ℂ) :
    rankOneExtensionTensorContraction ℓ (rankOneExtensionLowerPureTensor w z) =
      ℓ w * z.down := by
  change Shahidi.pairFunctional ULift.moduleEquiv.toLinearMap ℓ
    ((PiTensorProduct.reindex ℂ (Shahidi.pairCarrier (ULift.{uW} ℂ) W)
      Fin.revPerm).symm
      ((PiTensorProduct.reindex ℂ (Shahidi.pairCarrier (ULift.{uW} ℂ) W)
        Fin.revPerm) (Shahidi.pairTensor z w))) = _
  rw [LinearEquiv.symm_apply_apply, Shahidi.pairFunctional_pairTensor]
  exact mul_comm z.down (ℓ w)

end Tensor

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)

/-- Actual canonical normalized lower induction of `(σ, χLift)`. -/
abbrev rankOneExtensionLowerModel :=
  rankOneExtensionLowerInduced F t (rankOneExtensionCharacter.{uF, uW} F χ) σ

/-- Actual smooth covariant functions carrying the lower induced representation. -/
abbrev rankOneExtensionLowerSection :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
  (rankOneExtensionLowerModel F t χ σ).asModule

/-- Evaluate an actual lower induced section in its inducing tensor space. -/
def rankOneExtensionLowerSectionEval
    (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    rankOneExtensionLowerTensor (W := W) := by
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
  exact Induction.eval _ _ f g

/-- The contraction supplied by an inverse-character Whittaker functional on `σ`. -/
def rankOneExtensionWhittakerContraction
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (ℓ : letI := F.canonicalTopologicalData.topology;
      Whittaker.glInverseFunctionals ψ t σ) :
    rankOneExtensionLowerTensor (W := W) →ₗ[ℂ] ℂ :=
  rankOneExtensionTensorContraction ℓ.val

/-- The scalar coefficient of a section, for the specified inverse functional. -/
def rankOneExtensionLowerSectionCoefficient
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (ℓ : letI := F.canonicalTopologicalData.topology;
      Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) : ℂ :=
  rankOneExtensionWhittakerContraction F t σ ψ ℓ
    (rankOneExtensionLowerSectionEval F t χ σ f g)

end Padic

section Coordinates

variable {K : Type uF} [Field K]

/-- Keep the target's ambient rank `1 + (t + 1)`, with the large block first. -/
def rankOneExtensionCellCoordinates (t : ℕ) :
    Fin (t + 1) ⊕ Fin 1 ≃ Fin (1 + (t + 1)) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm (t + 1) 1))

def rankOneExtensionHeadIndex (t : ℕ) (i : Fin (t + 1)) :
    Fin (1 + (t + 1)) :=
  rankOneExtensionCellCoordinates t (Sum.inl i)

def rankOneExtensionScalarIndex (t : ℕ) : Fin (1 + (t + 1)) :=
  rankOneExtensionCellCoordinates t (Sum.inr 0)

@[simp] theorem rankOneExtensionScalarIndex_val (t : ℕ) :
    (rankOneExtensionScalarIndex t).val = t + 1 := by
  simp [rankOneExtensionScalarIndex, rankOneExtensionCellCoordinates, Nat.add_comm]

/-- The complementary upper cell `u(y) = [I, y; 0, 1]`. -/
def rankOneExtensionUpperCell (t : ℕ) (y : Fin (t + 1) → K) :
    Langlands.GeneralLinear (1 + (t + 1)) K :=
  reindex (R := K) (rankOneExtensionCellCoordinates t)
    { val := Matrix.fromBlocks 1 (Matrix.of fun i (_ : Fin 1) => y i) 0 1
      inv := Matrix.fromBlocks 1 (Matrix.of fun i (_ : Fin 1) => -y i) 0 1
      val_inv := by
        simp [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
        ext i j
        simp
      inv_val := by
        simp [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
        ext i j
        simp }

/-- The lower block `[m, 0; x, a]`, with the row `x` unscaled. -/
def rankOneExtensionLowerBlock (t : ℕ)
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K) (a : Kˣ) :
    Langlands.GeneralLinear (1 + (t + 1)) K :=
  reindex (R := K) (rankOneExtensionCellCoordinates t)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.fromBlocks m.val 0 (Matrix.of fun (_ : Fin 1) => x)
        (Matrix.of fun (_ _ : Fin 1) => a.val))
      (by
        rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_fin_one]
        exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero m) a.ne_zero))

/-- Full entry formula for the upper cell in the explicit block coordinates. -/
theorem rankOneExtensionUpperCell_apply (t : ℕ) (y : Fin (t + 1) → K)
    (i j : Fin (t + 1) ⊕ Fin 1) :
    rankOneExtensionUpperCell t y
        (rankOneExtensionCellCoordinates t i) (rankOneExtensionCellCoordinates t j) =
      Matrix.fromBlocks 1 (Matrix.of fun i (_ : Fin 1) => y i) 0 1 i j := by
  change Matrix.reindex _ _ _ _ _ = _
  simp

/-- Full entry formula for the lower block; no implicit permutation or rank cast. -/
theorem rankOneExtensionLowerBlock_apply (t : ℕ)
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K) (a : Kˣ)
    (i j : Fin (t + 1) ⊕ Fin 1) :
    rankOneExtensionLowerBlock t m x a
        (rankOneExtensionCellCoordinates t i) (rankOneExtensionCellCoordinates t j) =
      Matrix.fromBlocks m.val 0 (Matrix.of fun (_ : Fin 1) => x)
        (Matrix.of fun (_ _ : Fin 1) => a.val) i j := by
  change Matrix.reindex _ _ _ _ _ = _
  simp

@[simp] theorem rankOneExtensionLowerBlock_scalar (t : ℕ)
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K) (a : Kˣ) :
    rankOneExtensionLowerBlock t m x a
      (rankOneExtensionScalarIndex t) (rankOneExtensionScalarIndex t) = a.val :=
  rankOneExtensionLowerBlock_apply t m x a (Sum.inr 0) (Sum.inr 0)

/-- Append a positive rank identity block using the standard rank inclusion. -/
def rankOneExtensionEmbeddedLowerBlock (t k : ℕ)
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K) (a : Kˣ) :
    Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) K :=
  rankInclusion (k + 1) (rankOneExtensionLowerBlock t m x a)

/-- The first trailing coordinate, immediately after the scalar coordinate. -/
def rankOneExtensionFirstTrailingIndex (t k : ℕ) :
    Fin ((1 + (t + 1)) + (k + 1)) :=
  (0 : Fin (k + 1)).natAdd (1 + (t + 1))

private theorem scalar_ne_firstTrailing (t k : ℕ) :
    (rankOneExtensionScalarIndex t).castAdd (k + 1) ≠
      rankOneExtensionFirstTrailingIndex t k := by
  intro h
  have hv := congrArg Fin.val h
  simp [rankOneExtensionFirstTrailingIndex] at hv

/-- Right smearing by `I + u E_(t+1,t+2)` in zero-based matrix coordinates. -/
def rankOneExtensionSmearingUnipotent (t k : ℕ) (u : K) :
    Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) K where
  val := Matrix.transvection ((rankOneExtensionScalarIndex t).castAdd (k + 1))
    (rankOneExtensionFirstTrailingIndex t k) u
  inv := Matrix.transvection ((rankOneExtensionScalarIndex t).castAdd (k + 1))
    (rankOneExtensionFirstTrailingIndex t k) (-u)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same _ _ (scalar_ne_firstTrailing t k)]
    simp
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same _ _ (scalar_ne_firstTrailing t k)]
    simp

/-- Exact entries of the single-coordinate smearing unipotent. -/
theorem rankOneExtensionSmearingUnipotent_apply (t k : ℕ) (u : K)
    (i j : Fin ((1 + (t + 1)) + (k + 1))) :
    rankOneExtensionSmearingUnipotent t k u i j =
      (if i = j then 1 else 0) +
        if i = (rankOneExtensionScalarIndex t).castAdd (k + 1) ∧
            j = rankOneExtensionFirstTrailingIndex t k then u else 0 := by
  simp [rankOneExtensionSmearingUnipotent, Matrix.transvection,
    Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- The scalar Fourier pairing is `a * u`, with the plus sign. -/
theorem rankOneExtensionEmbeddedLowerBlock_mul_smearing_pairing (t k : ℕ)
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K)
    (a : Kˣ) (u : K) :
    (rankOneExtensionEmbeddedLowerBlock t k m x a *
      rankOneExtensionSmearingUnipotent t k u)
        ((rankOneExtensionScalarIndex t).castAdd (k + 1))
        (rankOneExtensionFirstTrailingIndex t k) = a.val * u := by
  change ((rankOneExtensionEmbeddedLowerBlock t k m x a).val *
    Matrix.transvection ((rankOneExtensionScalarIndex t).castAdd (k + 1))
      (rankOneExtensionFirstTrailingIndex t k) u)
    ((rankOneExtensionScalarIndex t).castAdd (k + 1))
    (rankOneExtensionFirstTrailingIndex t k) = _
  rw [Matrix.mul_transvection_apply_same]
  simp [rankOneExtensionEmbeddedLowerBlock, rankInclusion,
    rankOneExtensionFirstTrailingIndex, mul_comm]

end Coordinates

end Langlands.RankinSelberg
