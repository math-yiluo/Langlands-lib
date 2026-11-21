import Langlands.Representation.Archimedean.RealCartanPlacedWeights
import Langlands.Representation.Archimedean.RealCartanOffBlockProduct

/-! # The common normalized denominator on the real Cartan -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanSourceDenominator

open Langlands.LocalFactor.Archimedean RealCartanBlockLayout RealCartanFixedCosets
  RealCartanOffBlockDeterminant RealCartanPlacedTrace RealCartanPlacedWeights RealCartanRadialWeight
  RealCartanTraceCoordinates RealCartanTransverseDeterminant RealLeviChart RealLeviCompactChart
  RealStandardEllipticCartan

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

private theorem val_inv {n : ℕ} (u : K n) : ((u⁻¹ : K n) : M n) = (u : M n)ᵀ := by
  change star (u : M n) = _
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

private theorem mul_transpose_self {n : ℕ} (u : K n) : (u : M n) * (u : M n)ᵀ = 1 :=
  (mem_orthogonalGroup_iff _ _).mp u.2

private def scaleOrthogonal {n : ℕ} (a : ℝ) (ha : 0 < a) (u : K n) : (M n)ˣ where
  val := a • (u : M n)
  inv := a⁻¹ • (u : M n)ᵀ
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul,
      mul_transpose_self]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul,
      mul_eq_one_comm.mp (mul_transpose_self u)]

/-- The original Cartan block with its radial scalar, as a matrix unit. -/
def sourceBlockUnit {r s : ℕ} (x : Coordinates r s) (u : CartanSlot r s) : (M (slotSize u))ˣ :=
  scaleOrthogonal (Real.exp (coordinateRadius x u)) (Real.exp_pos _) (sourceSmall x u)

private theorem sourceBlockUnit_grams {r s : ℕ} (x : Coordinates r s) (u : CartanSlot r s) :
    (sourceBlockUnit x u).valᵀ * (sourceBlockUnit x u).val = (Real.exp (coordinateRadius x u))^2 • 1 ∧
      (sourceBlockUnit x u).val * (sourceBlockUnit x u).valᵀ = (Real.exp (coordinateRadius x u))^2 • 1 := by
  let U : M (slotSize u) := (sourceSmall x u).val
  let a := Real.exp (coordinateRadius x u)
  have hU : U * Uᵀ = 1 := mul_transpose_self (sourceSmall x u)
  change (a • U)ᵀ * (a • U) = a^2 • 1 ∧ (a • U) * (a • U)ᵀ = a^2 • 1
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU,
    mul_eq_one_comm.mp hU, pow_two, and_self]

/-- The normalized denominator depends only on the source Cartan blocks. -/
def sourceNormalizedProduct {r s : ℕ} (x : Coordinates r s) : ℝ :=
  normalizedOffBlockProduct slotSize (sourceBlockUnit x)

theorem sourceNormalizedProduct_ne_zero {r s : ℕ} {x : Coordinates r s}
    (hx : x ∈ separatedRegularCoordinates r s) : sourceNormalizedProduct x ≠ 0 := by
  apply normalizedOffBlockProduct_ne_zero_of_gram slotSize (sourceBlockUnit x)
    (fun u => (Real.exp (coordinateRadius x u)) ^ 2) (sourceBlockUnit_grams x)
  intro u v he
  apply hx.1
  simp only [pow_two, ← Real.exp_add] at he
  linarith [Real.exp_injective he]

private theorem normalizedProduct_reindexed {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : β ≃ α) (d : α → ℕ) (d' : β → ℕ)
    (m : ∀ i, Fin (d (e i)) ≃ Fin (d' i)) (g : ∀ i, (M (d i))ˣ) (k : ∀ i, (M (d' i))ˣ) :
    normalizedOffBlockProduct d' (fun i => k i * Units.map (reindexRingEquiv ℝ (m i)).toMonoidHom
      (g (e i)) * (k i)⁻¹) = normalizedOffBlockProduct d g := by
  rw [← normalizedOffBlockProduct_equiv e d g]
  unfold normalizedOffBlockProduct
  refine Finset.prod_congr rfl fun ⟨p, hp⟩ _ => ?_
  induction p using Sym2.ind with
  | _ i j =>
    change normalizedOffBlockDet (k i * Units.map (reindexRingEquiv ℝ (m i)).toMonoidHom
        (g (e i)) * (k i)⁻¹) (k j * Units.map (reindexRingEquiv ℝ (m j)).toMonoidHom
        (g (e j)) * (k j)⁻¹) = normalizedOffBlockDet (g (e i)) (g (e j))
    rw [normalizedOffBlockDet_conj]
    exact normalizedOffBlockDet_reindex (m i) (m j) (g (e i)) (g (e j))

section Placement

variable {r s t : ℕ} (b : Fin t → RealBlock) (h : 2 * r + s = ∑ i, blockSizes b i)
variable (x : Coordinates r s) (e : Assignment (blockSizes b) (cartanLabel h))
variable (κ : LeviFrame (blockSizes b))

local notation "Sizes" => blockSizes b
local notation "N" => ∑ i, Sizes i

private def placeLabel : Fin t ≃ CartanSlot r s := e.val.symm.trans finSumFinEquiv.symm

private theorem blockFrame_submatrix (v : LeviFrame Sizes) (i : Fin t) :
    ((blockFrame Sizes v : M N).submatrix (pos Sizes i) (pos Sizes i)) =
      (compactEquiv (Sizes i) (v i)).val := by
  ext p q
  exact blockDiagHom_pos_pos_self Sizes (fun j => (v j).val.val) i p q

private theorem scaledBlock_eq_source (i : Fin t) :
    let d := matchingRadius b h x e
    let B := fixedLeftFrame Sizes (matchedOrthogonal b h x e) κ
    let k := Unitary.toUnits (compactEquiv (Sizes i) (κ i))
    scaledBlock Sizes d (matchingRadius_pos b h x e) (blockFrame Sizes B) (blockZero_blockFrame Sizes B) i =
      k * Units.map (reindexRingEquiv ℝ (matchedIndexEquiv h e i)).toMonoidHom
        (sourceBlockUnit x (placeLabel b h e i)) * k⁻¹ := by
  intro d B k
  let Q := compactEquiv (Sizes i) (B i)
  let κi := compactEquiv (Sizes i) (κ i)
  let R := matchedSmall b h x e i
  let mi := matchedIndexEquiv h e i
  let u := matchedSlot h e i
  have hQ : Q⁻¹ = κi * R * κi⁻¹ := by
    change ((compactEquiv (Sizes i)) (κ i * (matchedOrthogonal b h x e i)⁻¹ * (κ i)⁻¹))⁻¹ = _
    simp only [map_mul, map_inv, κi, R, matchedSmall]
    group
  have hRadius : d i = Real.exp (coordinateRadius x u) := rfl
  have hblock : ((blockFrame Sizes B : M N).submatrix (pos Sizes i) (pos Sizes i)) = Q.val :=
    blockFrame_submatrix b B i
  have hR : R.val = Matrix.reindex mi mi (sourceSmall x u).val := matchedSmall_val b h x e i
  apply Units.ext
  change d i • (((blockFrame Sizes B : M N).submatrix (pos Sizes i) (pos Sizes i))ᵀ) =
    (κi : M (Sizes i)) * (Matrix.reindex mi mi
      (Real.exp (coordinateRadius x u) • (sourceSmall x u).val)) * (κi⁻¹ : K (Sizes i)).val
  rw [hblock, ← val_inv, hQ, hRadius]
  simp only [Submonoid.coe_mul]
  rw [hR]
  let X : M (Sizes i) := (sourceSmall x u).val.submatrix mi.symm mi.symm
  change Real.exp (coordinateRadius x u) • ((κi : M (Sizes i)) * X * (κi⁻¹ : K (Sizes i)).val) =
    (κi : M (Sizes i)) * (Real.exp (coordinateRadius x u) • X) * (κi⁻¹ : K (Sizes i)).val
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Every placed normalized product is the source denominator. -/
theorem matchedProduct_eq_source : matchedProduct b h x e κ = sourceNormalizedProduct x := by
  let B := fixedLeftFrame Sizes (matchedOrthogonal b h x e) κ
  let d := matchingRadius b h x e
  let U (i : Fin t) := scaledBlock Sizes d (matchingRadius_pos b h x e)
    (blockFrame Sizes B) (blockZero_blockFrame Sizes B) i
  let k (i : Fin t) := Unitary.toUnits (compactEquiv (Sizes i) (κ i))
  have hu (i : Fin t) : U i = k i * Units.map (reindexRingEquiv ℝ (matchedIndexEquiv h e i)).toMonoidHom
      (sourceBlockUnit x (placeLabel b h e i)) * (k i)⁻¹ := scaledBlock_eq_source b h x e κ i
  change (∏ ij : OffPair t, normalizedOffBlockDet (U ij.1.1) (U ij.1.2)) = _
  rw [← normalizedOffBlockProduct_eq_lower Sizes U, show U = _ from funext hu]
  exact normalizedProduct_reindexed (placeLabel b h e) slotSize Sizes (matchedIndexEquiv h e)
    (sourceBlockUnit x) k

end Placement

/-- The common normalized determinant for a separated regular source Cartan is nonzero. -/
def RealCartanSourceDenominatorStatement : Prop :=
  ∀ (r s : ℕ) (x : Coordinates r s), x ∈ separatedRegularCoordinates r s →
    sourceNormalizedProduct x ≠ 0 ∧
      ∀ (t : ℕ) (b : Fin t → RealBlock) (h : 2 * r + s = ∑ i, blockSizes b i)
        (e : Assignment (blockSizes b) (cartanLabel h)) (κ : LeviFrame (blockSizes b)),
        matchedProduct b h x e κ = sourceNormalizedProduct x

theorem realCartanSourceDenominator : RealCartanSourceDenominatorStatement :=
  fun _ _ x hx => ⟨sourceNormalizedProduct_ne_zero hx, fun _ b h e κ => matchedProduct_eq_source b h x e κ⟩

end Langlands.Archimedean.RealCartanSourceDenominator
